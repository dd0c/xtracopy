#!/usr/bin/perl
#
# xtracopy - replicate files and directories from this host to a pool of
#            remote hosts with scp.
#
#   * every file is kept on at least N remote hosts ("copies" in the config,
#     default 2), never more than one copy per host;
#   * new copies go to the hosts holding the fewest bytes, so the pool fills
#     up evenly;
#   * a state file records the size, mtime and MD5 of every file and which
#     hosts hold which version, so re-running the script only sends what
#     changed (changed files are refreshed on the hosts that already hold
#     them) and tops up copies that were lost.
#
# Written for Solaris 10 (perl 5.8.4, Sun SSH) and uses core modules only.
# Remote hosts need sshd, scp and perl (only perl for --verify).
#
# Run "xtracopy.pl --help" for usage.
#
use strict;
use warnings;

use Cwd qw(abs_path);
use Digest::MD5;
use Fcntl qw(:flock);
use File::Basename qw(basename dirname);
use File::Find;
use File::Spec;
use Getopt::Long;
use IPC::Open2;
use POSIX qw(strftime);

my $VERSION    = '1.0';
my $ME         = basename($0);
my $SCRIPT_DIR = dirname(abs_path($0));

# Sent to the remote perl on stdin by --verify: reads %-encoded paths after
# __END__ and prints one MD5 (or "-" if unreadable) per path, in order.
# It reads all input before printing anything, so the pipes cannot deadlock.
my $REMOTE_MD5_SCRIPT = <<'EOS';
use strict;
use Digest::MD5;
my @paths = <DATA>;
for my $p (@paths) {
    chomp $p;
    $p =~ s/%([0-9A-F]{2})/chr(hex($1))/ge;
    my $sum = '-';
    if (-f $p && open(my $fh, '<', $p)) {
        binmode $fh;
        my $d = eval { Digest::MD5->new->addfile($fh)->hexdigest };
        $sum = $d if defined $d;
        close $fh;
    }
    print "$sum\n";
}
__END__
EOS

#----------------------------------------------------------------------------
# Command line and configuration
#----------------------------------------------------------------------------

my %opt = (config => "$SCRIPT_DIR/xtracopy.conf");
GetOptions(\%opt,
    'config|c=s', 'dry-run|n', 'verbose|v', 'verify', 'prune', 'rehash',
    'status', 'help|h', 'version',
) or usage(2);
usage(0) if $opt{help};
if ($opt{version}) { print "$ME $VERSION\n"; exit 0 }
my $DRY = $opt{'dry-run'} ? 1 : 0;

my %cfg = read_config($opt{config});
my @HOSTS    = map { $_->{name} } @{ $cfg{hosts} };
my %HOST_DIR = map { $_->{name} => $_->{dir} } @{ $cfg{hosts} };
my @SSH_OPTS = split ' ', $cfg{ssh_opts};
my @SCP_OPTS = split ' ', $cfg{scp_opts};

my $COPIES = $cfg{copies};
if ($COPIES > @HOSTS) {
    warnmsg("copies = $COPIES but only " . scalar(@HOSTS)
          . " host(s) configured; keeping one copy on every host");
    $COPIES = scalar @HOSTS;
}

my $STATE_FILE = $cfg{state_file} =~ m{^/} ? $cfg{state_file}
               : "$SCRIPT_DIR/$cfg{state_file}";

# Sources from the command line replace those in the config file.
my $CMDLINE_SOURCES = @ARGV ? 1 : 0;
my @SOURCES = map { canon_path($_) } ($CMDLINE_SOURCES ? @ARGV : @{ $cfg{sources} });
my @EXCLUDES = @{ $cfg{excludes} };

#----------------------------------------------------------------------------
# Main
#----------------------------------------------------------------------------

my $interrupted = 0;
$SIG{INT} = $SIG{TERM} = $SIG{HUP} = sub { $interrupted = 1 };

my %state;    # path => { size, mtime, md5, copies => { host => md5 } }

# Hold an exclusive lock for the whole run so two runs cannot race on the
# state file.
open(my $LOCK, '>>', "$STATE_FILE.lock")
    or die "$ME: cannot open lock file $STATE_FILE.lock: $!\n";
flock($LOCK, LOCK_EX | LOCK_NB)
    or die "$ME: another $ME run holds $STATE_FILE.lock\n";

load_state();

if ($opt{status}) {
    show_status();
    exit 0;
}

die "$ME: no sources given (config 'source =' lines or command line)\n"
    unless @SOURCES;

my $errors = 0;
my %stats  = (new => 0, update => 0, bytes => 0, pruned => 0);

msg(sprintf("%s %s: %s%d host(s), %d source(s), %d copies per file",
    $ME, timestamp(), $DRY ? '(dry run) ' : '', scalar @HOSTS,
    scalar @SOURCES, $COPIES));

# 1. Scan the sources and (re)hash new or changed files.
my %found = scan_sources(\@SOURCES);
my %skip;
hash_files();
bail_if_interrupted();

# 2. Forget copies on hosts no longer in the config.
forget_unknown_hosts();

# 3. Find out which hosts are reachable.
my %up = check_hosts();
bail_if_interrupted();

# 4. Optionally check that the remote copies are really there and intact.
verify_copies() if $opt{verify};
bail_if_interrupted();

# 5. Decide what goes where, then copy.
my %todo = plan_copies();
do_copies(\%todo);
bail_if_interrupted();

# 6. Deal with files that disappeared from the sources.
handle_vanished();

save_state();
exit report();

#----------------------------------------------------------------------------
# Steps
#----------------------------------------------------------------------------

sub scan_sources {
    my ($sources) = @_;
    my %files;

    my $add = sub {
        my ($p) = @_;
        my @l = lstat($p) or return;
        my @st = @l;
        if (-l _) {
            @st = stat($p);
            if (!@st || !-f _) {
                vmsg("skipping symlink $p (not a link to a regular file)");
                return;
            }
        }
        elsif (!-f _) {
            vmsg("skipping $p (not a regular file)") unless -d _;
            return;
        }
        $files{$p} = [ $st[7], $st[9] ];    # size, mtime
    };

    for my $src (@$sources) {
        if (!-e $src) {
            warnmsg("source $src does not exist");
            $errors++;
            next;
        }
        next if excluded($src);
        if (-d $src) {
            find({ no_chdir => 1, wanted => sub {
                my $p = $File::Find::name;
                if ($p ne $src && excluded($p)) {
                    $File::Find::prune = 1 if -d $p;
                    return;
                }
                return if -d $p && !-l $p;
                $add->($p);
            } }, $src);
        }
        else {
            $add->($src);
        }
    }
    return %files;
}

sub hash_files {
    my $hashed = 0;
    for my $p (sort keys %found) {
        last if $interrupted;
        my ($size, $mtime) = @{ $found{$p} };
        my $e = $state{$p};
        next if !$opt{rehash} && $e && defined $e->{md5}
             && $e->{size} == $size && $e->{mtime} == $mtime;

        my $md5 = md5_file($p);
        if (!defined $md5) {
            warnmsg("cannot read $p: $!; skipped");
            $skip{$p} = 1;
            $errors++;
            next;
        }
        $e = $state{$p} ||= { copies => {} };
        vmsg("changed: $p") if defined $e->{md5} && $e->{md5} ne $md5;
        @$e{qw(size mtime md5)} = ($size, $mtime, $md5);
        $hashed++;
    }
    vmsg("hashed $hashed new or changed file(s)");
}

sub forget_unknown_hosts {
    my %known = map { $_ => 1 } @HOSTS;
    my %gone;
    for my $e (values %state) {
        for my $h (keys %{ $e->{copies} }) {
            next if $known{$h};
            delete $e->{copies}{$h};
            $gone{$h}++;
        }
    }
    for my $h (sort keys %gone) {
        warnmsg("host $h is no longer configured; forgetting its $gone{$h} "
              . "copies (the files are left on $h)");
    }
}

sub check_hosts {
    my %ok;
    for my $h (@HOSTS) {
        my $dir = rq($HOST_DIR{$h});
        my $cmd = $DRY ? "test -d $dir || true"
                       : "mkdir -p $dir && test -w $dir";
        if (spawn(1, ssh_cmd($h, $cmd))) {
            $ok{$h} = 1;
        }
        else {
            warnmsg("host $h is unreachable or $HOST_DIR{$h} is not writable; "
                  . "skipping it this run");
            $errors++;
        }
        last if $interrupted;
    }
    msg("hosts up: " . (join(' ', grep { $ok{$_} } @HOSTS) || 'none')
        . (@HOSTS > keys %ok
           ? "; down: " . join(' ', grep { !$ok{$_} } @HOSTS) : ''));
    return %ok;
}

sub verify_copies {
    for my $h (grep { $up{$_} } @HOSTS) {
        last if $interrupted;
        my @paths = sort grep { exists $state{$_}{copies}{$h} } keys %state;
        next unless @paths;
        msg("verifying " . scalar(@paths) . " copies on $h");
        my $sums = remote_md5($h, [ map { remote_path($h, $_) } @paths ]);
        if (!$sums) {
            warnmsg("verification on $h failed; its copies are left as recorded");
            $errors++;
            next;
        }
        my $bad = 0;
        for my $i (0 .. $#paths) {
            my $e = $state{ $paths[$i] };
            next if $sums->[$i] eq $e->{copies}{$h};
            msg("  $h: copy of $paths[$i] is "
                . ($sums->[$i] eq '-' ? 'missing' : 'modified'));
            delete $e->{copies}{$h};
            $bad++;
        }
        msg("  $h: $bad bad copies will be replaced") if $bad;
    }
}

# Returns host => [ [path, 'new'|'update'], ... ]
sub plan_copies {
    my %load = map { $_ => 0 } @HOSTS;    # bytes held per host
    for my $e (values %state) {
        $load{$_} += $e->{size} for keys %{ $e->{copies} };
    }

    my %plan;
    for my $p (sort keys %found) {
        next if $skip{$p};
        my $e = $state{$p};
        my $good = 0;

        # Refresh outdated copies where they already are.
        for my $h (sort keys %{ $e->{copies} }) {
            if ($e->{copies}{$h} eq $e->{md5}) {
                $good++;
            }
            elsif ($up{$h}) {
                push @{ $plan{$h} }, [ $p, 'update' ];
                $good++;
            }
            else {
                vmsg("$p: outdated copy on unreachable host $h");
            }
        }

        # Top up to the required number of copies on the emptiest hosts.
        my $need = $COPIES - $good;
        next if $need <= 0;
        my @cand = sort { $load{$a} <=> $load{$b} || $a cmp $b }
                   grep { $up{$_} && !exists $e->{copies}{$_} } @HOSTS;
        for my $h (splice(@cand, 0, $need)) {
            push @{ $plan{$h} }, [ $p, 'new' ];
            $load{$h} += $e->{size};
        }
    }
    return %plan;
}

sub do_copies {
    my ($plan) = @_;
    for my $h (sort keys %$plan) {
        last if $interrupted;
        my %kind  = map { $_->[0] => $_->[1] } @{ $plan->{$h} };
        my %bydir;
        push @{ $bydir{ dirname($_) } }, $_ for keys %kind;
        my @dirs = sort keys %bydir;

        msg(sprintf("%s: copying %d file(s)", $h, scalar keys %kind));

        # Create all target directories first, a chunk at a time.
        my $mkdir_ok = 1;
        for (my $i = 0; $i < @dirs && $mkdir_ok; $i += 100) {
            my @chunk = @dirs[ $i .. min($i + 99, $#dirs) ];
            $mkdir_ok = run(ssh_cmd($h, 'mkdir -p '
                . join(' ', map { rq(remote_path($h, $_)) } @chunk)));
        }
        if (!$mkdir_ok) {
            warnmsg("$h: cannot create target directories; skipping host");
            $errors++;
            next;
        }

        my $copy_ok = sub {
            for my $p (@_) {
                my $e = $state{$p};
                $e->{copies}{$h} = $e->{md5};
                $stats{ $kind{$p} }++;
                $stats{bytes} += $e->{size};
                vmsg("  $kind{$p}: $p -> $h");
            }
        };

        for my $d (@dirs) {
            my @files = sort @{ $bydir{$d} };
            my $target = "$h:" . scp_path(remote_path($h, $d) . '/');
            while (my @batch = splice(@files, 0, $cfg{batch_size})) {
                last if $interrupted;
                if (run($cfg{scp}, @SCP_OPTS, @batch, $target)) {
                    $copy_ok->(@batch);
                    next;
                }
                # Batch failed: retry one by one so a single bad file does
                # not hold back the rest.
                for my $p (@batch) {
                    last if $interrupted;
                    if (@batch > 1 && run($cfg{scp}, @SCP_OPTS, $p, $target)) {
                        $copy_ok->($p);
                    }
                    else {
                        warnmsg("$h: failed to copy $p");
                        $errors++;
                    }
                }
            }
        }
        save_state();    # keep progress even if a later host hangs
    }
}

sub handle_vanished {
    my @gone = sort grep { !$found{$_} && !$skip{$_} } keys %state;
    return unless @gone;

    if (!$opt{prune}) {
        msg(scalar(@gone) . " tracked file(s) no longer exist in the sources; "
          . "their remote copies are kept (use --prune to delete them)");
        vmsg("  vanished: $_") for @gone;
        return;
    }

    # Never prune because a whole source tree is missing (e.g. an unmounted
    # filesystem), and with sources on the command line only prune inside them.
    my @prunable = grep {
        my $root = source_root($_);
        defined $root ? -e $root : !$CMDLINE_SOURCES;
    } @gone;
    if (@prunable < @gone) {
        msg(scalar(@gone) - scalar(@prunable)
          . " vanished file(s) not pruned: their source is missing or not selected");
    }

    my %byhost;
    for my $p (@prunable) {
        push @{ $byhost{$_} }, $p for keys %{ $state{$p}{copies} };
        delete $state{$p} unless keys %{ $state{$p}{copies} };
    }
    for my $h (sort keys %byhost) {
        if (!$up{$h}) {
            msg("$h is down; its copies of vanished files will be pruned later");
            next;
        }
        my @paths = @{ $byhost{$h} };
        msg("$h: removing " . scalar(@paths) . " copies of vanished files");
        while (my @chunk = splice(@paths, 0, 100)) {
            last if $interrupted;
            if (run(ssh_cmd($h, 'rm -f '
                    . join(' ', map { rq(remote_path($h, $_)) } @chunk)))) {
                for my $p (@chunk) {
                    delete $state{$p}{copies}{$h};
                    delete $state{$p} unless keys %{ $state{$p}{copies} };
                    $stats{pruned}++;
                    vmsg("  removed: $p from $h");
                }
            }
            else {
                warnmsg("$h: failed to remove some copies");
                $errors++;
            }
        }
    }
}

sub report {
    my ($files, $bytes, @under) = (0, 0);
    for my $p (sort keys %found) {
        next if $skip{$p};
        my $e = $state{$p};
        $files++;
        $bytes += $e->{size};
        my $good = grep { $e->{copies}{$_} eq $e->{md5} } keys %{ $e->{copies} };
        push @under, "$p ($good of $COPIES)" if $good < $COPIES;
    }
    my $would = $DRY ? 'would copy' : 'copied';
    msg(sprintf("%s %s: %d file(s), %s; %s %d new + %d updated copies (%s)%s",
        $ME, timestamp(), $files, human($bytes), $would, $stats{new},
        $stats{update}, human($stats{bytes}),
        $stats{pruned} ? ", pruned $stats{pruned}" : ''));
    if (@under) {
        warnmsg(scalar(@under) . " file(s) have fewer than $COPIES current copies:");
        print STDERR "    $_\n" for @under[ 0 .. min(19, $#under) ];
        print STDERR "    ...\n" if @under > 20;
    }
    msg("errors: $errors") if $errors;
    return ($errors || @under) ? 1 : 0;
}

sub show_status {
    my (%count, %bytes, $under, $total);
    for my $p (sort keys %state) {
        my $e = $state{$p};
        my @c = map { $e->{copies}{$_} eq $e->{md5} ? $_ : "$_(outdated)" }
                sort keys %{ $e->{copies} };
        my $good = grep { !/\(outdated\)$/ } @c;
        $under++ if $good < $COPIES;
        $total++;
        for my $h (keys %{ $e->{copies} }) {
            $count{$h}++;
            $bytes{$h} += $e->{size};
        }
        printf "%s %10s  %s  %s\n", ($good < $COPIES ? '!' : ' '),
            human($e->{size}), $p, join(' ', @c) || '(no copies)';
    }
    print "\n";
    printf "%-20s %8d files %10s\n", $_, $count{$_} || 0, human($bytes{$_} || 0)
        for @HOSTS;
    printf "\n%d tracked file(s), %d with fewer than %d current copies (marked !)\n",
        $total || 0, $under || 0, $COPIES;
}

#----------------------------------------------------------------------------
# Config and state files
#----------------------------------------------------------------------------

sub read_config {
    my ($file) = @_;
    my %c = (
        copies      => 2,
        remote_dir  => undef,
        ssh         => '/usr/bin/ssh',
        scp         => '/usr/bin/scp',
        ssh_opts    => '-o BatchMode=yes',
        scp_opts    => '-p -q -o BatchMode=yes',
        scp_quote   => 'yes',
        remote_perl => 'perl',
        state_file  => 'xtracopy.state',
        batch_size  => 50,
    );
    my (@hosts, @sources, @excludes, %seen);

    open(my $fh, '<', $file) or die "$ME: cannot read config $file: $!\n";
    while (my $line = <$fh>) {
        chomp $line;
        $line =~ s/^\s+//;
        $line =~ s/\s+$//;
        next if $line eq '' || $line =~ /^#/;
        my ($k, $v) = $line =~ /^(\w+)\s*=\s*(.*)$/
            or die "$ME: $file line $.: cannot parse '$line'\n";
        if ($k eq 'host') {
            my ($name, $dir) = split ' ', $v, 2;
            die "$ME: $file line $.: bad host name '$v'\n"
                unless defined $name && $name =~ /^[\w.\-@]+$/;
            die "$ME: $file line $.: host $name listed twice\n" if $seen{$name}++;
            push @hosts, { name => $name, dir => $dir };
        }
        elsif ($k eq 'source')  { push @sources, $v }
        elsif ($k eq 'exclude') {
            my $re = eval { qr/$v/ }
                or die "$ME: $file line $.: bad exclude regex '$v': $@\n";
            push @excludes, $re;
        }
        elsif (exists $c{$k}) { $c{$k} = $v }
        else { die "$ME: $file line $.: unknown setting '$k'\n" }
    }
    close $fh;

    die "$ME: $file: no 'host =' lines\n" unless @hosts;
    die "$ME: $file: copies must be a whole number >= 1\n"
        unless $c{copies} =~ /^\d+$/ && $c{copies} >= 1;
    die "$ME: $file: batch_size must be a whole number >= 1\n"
        unless $c{batch_size} =~ /^\d+$/ && $c{batch_size} >= 1;
    for my $h (@hosts) {
        $h->{dir} = $c{remote_dir} unless defined $h->{dir};
        die "$ME: $file: no remote_dir for host $h->{name}\n"
            unless defined $h->{dir};
        die "$ME: $file: remote dir '$h->{dir}' for $h->{name} must be absolute\n"
            unless $h->{dir} =~ m{^/};
        $h->{dir} =~ s{/+$}{};
    }
    $c{hosts}    = \@hosts;
    $c{sources}  = \@sources;
    $c{excludes} = \@excludes;
    return %c;
}

sub load_state {
    return unless -e $STATE_FILE;
    open(my $fh, '<', $STATE_FILE) or die "$ME: cannot read $STATE_FILE: $!\n";
    while (my $line = <$fh>) {
        next if $line =~ /^#/ || $line !~ /\S/;
        chomp $line;
        my ($p, $size, $mtime, $md5, $copies) = split /\t/, $line, -1;
        die "$ME: $STATE_FILE line $.: corrupt entry\n"
            unless defined $copies && $md5 =~ /^[0-9a-f]{32}$/;
        my %c;
        if ($copies ne '-') {
            for (split /,/, $copies) {
                my ($h, $sum) = split /=/, $_, 2;
                $c{$h} = $sum;
            }
        }
        $state{ dec($p) } = { size => $size, mtime => $mtime, md5 => $md5,
                              copies => \%c };
    }
    close $fh;
}

sub save_state {
    return if $DRY;
    my $tmp = "$STATE_FILE.tmp.$$";
    open(my $fh, '>', $tmp) or die "$ME: cannot write $tmp: $!\n";
    print $fh "# $ME state, written ", timestamp(), " - do not edit while $ME runs\n",
              "# path\tsize\tmtime\tmd5\thost=md5,...\n";
    for my $p (sort keys %state) {
        my $e = $state{$p};
        # Files that are gone locally and have no copies left are forgotten.
        next if !$found{$p} && !keys %{ $e->{copies} };
        my $c = join(',', map { "$_=$e->{copies}{$_}" } sort keys %{ $e->{copies} });
        print $fh join("\t", enc($p), $e->{size}, $e->{mtime}, $e->{md5},
                       $c eq '' ? '-' : $c), "\n";
    }
    close($fh) or die "$ME: cannot write $tmp: $!\n";
    rename($tmp, $STATE_FILE) or die "$ME: cannot rename $tmp: $!\n";
}

#----------------------------------------------------------------------------
# Helpers
#----------------------------------------------------------------------------

sub md5_file {
    my ($p) = @_;
    open(my $fh, '<', $p) or return undef;
    binmode $fh;
    my $d = eval { Digest::MD5->new->addfile($fh)->hexdigest };
    close $fh;
    return $d;
}

# Run "perl" on the remote host and get the MD5 of each path (or "-").
sub remote_md5 {
    my ($h, $paths) = @_;
    local $SIG{PIPE} = 'IGNORE';
    my ($out, $in);
    my $pid = eval { open2($out, $in, ssh_cmd($h, $cfg{remote_perl})) };
    return undef unless $pid;
    print $in $REMOTE_MD5_SCRIPT;
    print $in enc($_), "\n" for @$paths;
    close $in;
    my @sums = <$out>;
    close $out;
    waitpid($pid, 0);
    return undef if $? != 0 || @sums != @$paths;
    chomp @sums;
    return \@sums;
}

sub ssh_cmd {
    my ($h, $remote_cmd) = @_;
    return ($cfg{ssh}, @SSH_OPTS, $h, $remote_cmd);
}

sub remote_path {
    my ($h, $p) = @_;
    return $p eq '/' ? $HOST_DIR{$h} : $HOST_DIR{$h} . $p;
}

# Quote a string for the remote shell (works for sh, ksh and csh).
sub rq {
    my ($s) = @_;
    $s =~ s/'/'\\''/g;
    return "'$s'";
}

# The classic scp protocol (Sun SSH, OpenSSH < 9) passes the target through
# the remote shell; scp in SFTP mode (OpenSSH >= 9 default) does not.
sub scp_path {
    my ($p) = @_;
    return $cfg{scp_quote} =~ /^(yes|1|true)$/i ? rq($p) : $p;
}

# Run a command that changes something; only echoed in dry-run mode.
sub run {
    my @cmd = @_;
    vmsg('  + ' . join(' ', @cmd));
    return 1 if $DRY;
    return spawn(0, @cmd);
}

# fork/exec instead of system() so ^C reaches our handler too and we can
# stop cleanly between batches.
sub spawn {
    my ($quiet, @cmd) = @_;
    my $pid = fork;
    if (!defined $pid) {
        warnmsg("fork failed: $!");
        return 0;
    }
    if ($pid == 0) {
        open(STDIN, '<', '/dev/null');
        if ($quiet) {
            open(STDOUT, '>', '/dev/null');
            open(STDERR, '>', '/dev/null');
        }
        exec { $cmd[0] } @cmd
            or print STDERR "$ME: cannot run $cmd[0]: $!\n";
        POSIX::_exit(127);
    }
    waitpid($pid, 0);
    return $? == 0;
}

sub canon_path {
    my ($p) = @_;
    $p = File::Spec->rel2abs($p);
    $p = File::Spec->canonpath($p);
    return $p;
}

sub excluded {
    my ($p) = @_;
    for my $re (@EXCLUDES) {
        return 1 if $p =~ $re;
    }
    return 0;
}

# The configured source a path belongs to (longest match), or undef.
sub source_root {
    my ($p) = @_;
    my $best;
    for my $s (@SOURCES) {
        next unless $p eq $s || index($p, $s eq '/' ? '/' : "$s/") == 0;
        $best = $s if !defined $best || length($s) > length($best);
    }
    return $best;
}

# %-encode characters that would break the tab/line based formats.
sub enc {
    my ($s) = @_;
    $s =~ s/([%\t\n\r])/sprintf('%%%02X', ord($1))/ge;
    return $s;
}

sub dec {
    my ($s) = @_;
    $s =~ s/%([0-9A-F]{2})/chr(hex($1))/ge;
    return $s;
}

sub bail_if_interrupted {
    return unless $interrupted;
    save_state();
    warnmsg("interrupted; progress saved");
    exit 130;
}

sub human {
    my ($n) = @_;
    my @u = ('B', 'KB', 'MB', 'GB', 'TB');
    my $i = 0;
    while ($n >= 1024 && $i < $#u) { $n /= 1024; $i++ }
    return $i ? sprintf('%.1f %s', $n, $u[$i]) : "$n B";
}

sub min { return $_[0] < $_[1] ? $_[0] : $_[1] }

sub timestamp { return strftime('%Y-%m-%d %H:%M:%S', localtime) }
sub msg       { print "@_\n" }
sub vmsg      { print "@_\n" if $opt{verbose} }
sub warnmsg   { print STDERR "$ME: @_\n" }

sub usage {
    my ($rc) = @_;
    my $fh = $rc ? \*STDERR : \*STDOUT;
    print $fh <<"EOT";
Usage: $ME [options] [path ...]

Copies the configured files and directories to the remote hosts in the
config file with scp, keeping at least 'copies' copies of every file, each
on a different host. Re-run it whenever the sources change: only new and
changed files are sent, and lost copies are replaced.

Paths given on the command line replace the 'source' lines in the config.

Options:
  -c, --config FILE  config file (default: xtracopy.conf next to the script)
  -n, --dry-run      show what would be done; change nothing
  -v, --verbose      list every file and command
      --verify       check the remote copies' MD5 sums over ssh (needs perl
                     on the remote hosts) and replace missing/modified ones
      --prune        delete remote copies of files removed from the sources
      --rehash       re-checksum all local files, not only changed ones
      --status       show where every file is stored (from the state file)
  -h, --help         this help
      --version      print the version

Exit status: 0 all files have enough current copies; 1 errors or files
with too few copies; 2 usage error; 130 interrupted.
EOT
    exit $rc;
}
