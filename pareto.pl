#!/bin/perl -s

use utf8;
use v5.36;
use warnings;
use Data::Dumper;
use Digest::MD5 qw(md5_base64);
use Memoize;
use List::Util qw(min max any all sum product first);
use JSON qw(decode_json);
use IPC::Open3;


our ($h, $u, $n, $o, $g, $m);

sub slurp($filename, $binmode = 0) {
	open my $fh, '<', $filename;
	binmode($fh) if $binmode;
	local $/;
	return <$fh>;
}

sub write_file($filename, $data, $binmode = 0) {
	open my $fh, '>', $filename;
	binmode($fh) if $binmode;
	print $fh $data;
}

sub wget($url, $filename, $force = 0) {
	$url =~ y/\\'//;
	$filename =~ y/\\'//;
	`wget '$url' -O '$filename'` unless -f $filename and not $force;
}

sub parse_nplet($score) {
	my @nplet = $score->@{qw(trackless cycles cost area instructions height width rate rate areaINF heightINF widthINF)};
	$nplet[0] = 1 - $nplet[0];
	$nplet[7] = defined $nplet[7] ? 0 : 1;
	$_ = ($_ // 99999) + 0 for @nplet;
	return \@nplet;
}

sub mask_to_list($mask) {
	return grep { ($mask >> $_) & 1 } 0..7;
}

sub mask_to_letters($mask) {
	my @letters = qw(T C G A I H W R)[mask_to_list($mask)];
	local $" = '';
	return $#letters ? "(@letters)" : "@letters";
}

sub get_masks() {
	return sort {
		mask_to_list($a) <=> mask_to_list($b) ||
		$a <=> $b
	} (1, map { 2 * $_ } 1..127);
}

memoize($_) for qw(mask_to_list mask_to_letters get_masks);

sub is_superset_of_any($a, @b) {
	return any { ($_ & ~$a) == 0 } @b;
}

sub is_pareto($this, $mask, $context) {
	my @metrics = mask_to_list($mask);
	my @ties = ();

	for my $that (@$context) {
		my $dominated = 1;
		my $tied = 1;
		for my $metric (@metrics) {
			my ($a, $b) = ($this->[$metric], $that->[$metric]);
			$tied = 0 if $b != $a;
			$dominated = 0 if $b > $a;
		}
		return if $dominated and not $tied;
		push @ties, $that if $tied;
	}

	return 1, @ties;
}

sub get_suffix($nplet, $mask, $context) {
	return '' if ($mask & ($mask - 1)) == 0;
	my @metrics = mask_to_list($mask);
	my $sum = sum @$nplet[@metrics];
	my $product = product @$nplet[@metrics];
	return '⁺' if all { $sum <= sum @$_[@metrics] } @$context;
	return 'ˣ' if all { $product <= product @$_[@metrics] } @$context;
}

sub name($nplet, $context, $ban_mask = 0) {
	return "" if @$context == 0 or (@$context == 1 and $context->[0] == $nplet);

	my @good_masks = ();
	my @good_names = ();
	my $future_ban_mask = 1;

	for my $mask (get_masks()) {
		next if is_superset_of_any($mask, @good_masks);
		next if ($mask & $ban_mask) != 0;
		my ($good, @ties) = is_pareto($nplet, $mask, $context);
		if ($good) {
			my $letters = mask_to_letters($mask);
			$letters .= get_suffix($nplet, $mask, $context) // '';
			$future_ban_mask |= $mask if ($mask & ($mask - 1)) == 0;
			push @good_masks, $mask;
			push @good_names, "$letters$_" for name($nplet, \@ties, $ban_mask | $mask | $future_ban_mask);
		}
	}

	return @good_names;
}

sub compare_names($a, $b) {
	my ($a1, $b1) = map { sum map 1.5**y///c, /[A-Z]|\([A-Z]+\)/g } $a, $b;
	return ($a1 <=> $b1) if $a1 != $b1;
	my ($a2, $b2) = map { y/)TCGAIHWR(/A-J/r } $a, $b;
	return $a2 cmp $b2;
}

sub is_substring($this, $that) {
	return 0 if length($this) >= length($that);
	my $last_index = -1;
	while ($this =~ /[A-Z]/g) {
		my $letter = $&;
		return 0 unless $that =~ /$letter/;
		return 0 unless $-[0] >= $last_index;
		$last_index = $-[0];
	}
	return 1;
}

sub is_superstring_of_any($string, @strings) {
	return any { is_substring($_, $string) } @strings;
}

sub nplet_to_filename {
	my $result = "$_[2]g$_[1]c$_[3]a$_[4]i$_[5]h$_[6]w$_[8]r";
	return ($result =~ s(99999r)()gr) . ($_[0] ? '' : 'T');
}

sub solution_to_parts($sol) {
	(my ($magic, $level, $sol_name, $part_count), $sol) = unpack 'LC/aC/aL/(x8)La*', $sol;
	die "$magic != 7" if $magic != 7;
	# die "$level ne 'P007'" if $level ne 'P007';
	return map {
		(my ($part_name, $magic, $x, $y, $size, $rotation, $ionum, $instr_count), $sol) = unpack 'C/aCllLlLLa*', $sol;
		die "$magic != 1" if $magic != 1;
		$rotation %= 6;
		my $instructions = '';
		for (1..$instr_count) {
			(my ($offset, $instruction), $sol) = unpack 'LCa*', $sol;
			vec($instructions, $offset, 8) = $instruction;
		}

		my $result = {
			part_name => $part_name,
			x => $x,
			y => $y,
			size => $size,
			rotation => $rotation,
			instructions => $instructions,
		};

		if ($part_name eq 'track') {
			my @track_data = unpack 'L/(ll)a*', $sol;
			$sol = pop @track_data;

			my @track = ();
			while (@track_data) {
				my ($dx, $dy) = splice @track_data, 0, 2;
				push @track, [$x + $dx, $y + $dy];
			}
			($result->{x}, $result->{y}) = $track[0]->@*;
			$result->{track} = \@track;
		}
		(my ($armnum), $sol) = unpack 'La*', $sol;
		$result
	} 1..$part_count;
}

sub parts_to_solution(@parts) {
	my $sol = pack 'LC/aC/aLL', 7, 'P007', 'PARETO', 0, 0+@parts;
	my $arm_count = 0;
	my $input_count = 0;

	for (@parts) {
		my $ionum = $_->{part_name} eq 'input' ? $input_count++ : 0;
		my $armnum = $_->{part_name} =~ /^(arm[1236]|piston|baron)$/ ? $arm_count++ : 0;
		my $instruction_count = $_->{instructions} =~ y/\0//c;
		$sol .= pack 'C/aCllLlLL', $_->{part_name}, 1, $_->{x}, $_->{y}, $_->{size}, $_->{rotation}, $ionum, $instruction_count;
		$sol .= pack 'La', $-[0], $& while $_->{instructions} =~ /\w/g;
		if ($_->{part_name} eq 'track') {
			my @track_data = ();
			for my $point ($_->{track}->@*) {
				push @track_data, $point->[0] - $_->{x}, $point->[1] - $_->{y};
			}
			$sol .= pack 'LL*', @track_data / 2, @track_data;
		}
		$sol .= pack 'L', $armnum;
	}
	return $sol;
}

sub translate_parts($parts, $dx, $dy) {
	for my $part (@$parts) {
		$part->{x} += $dx;
		$part->{y} += $dy;
		map { $_->[0] += $dx; $_->[1] += $dy } ($part->{track} // [])->@*;
	}
}

my @xy_rotations = (
	[ 1,  0,  0,  1],
	[ 0, -1,  1,  1],
	[-1, -1,  1,  0],
	[-1,  0,  0, -1],
	[ 0,  1, -1, -1],
	[ 1,  1, -1,  0],
);

sub rotate_parts($parts, $rotation) {
	my ($xfx, $xfy, $yfx, $yfy) = @{$xy_rotations[$rotation]};
	for my $part (@$parts) {
		$part->{rotation} += $rotation;
		my ($x, $y) = ($part->{x}, $part->{y});
		$part->{x} = $x * $xfx + $y * $xfy;
		$part->{y} = $x * $yfx + $y * $yfy;
	}
}

sub mirror_parts($parts) {
	for my $part (@$parts) {
		$part->{x} += $part->{y};
		$part->{y} *= -1;
		$part->{rotation} = -$part->{rotation};
		$part->{instructions} =~ y/PRpr/prPR/;
		$_->[0] += $_->[1], $_->[1] *= -1 for ($part->{track} // [])->@*;
	}
}

my %rotational_symmetry = (
	input => 1,
	"glyph-calcification" => 1,
	"bonder-speed" => 2,
	arm2 => 3,
	arm3 => 2,
	arm6 => 1,
);

# P = pivot right
# E = extend
# G = grab
# A = advance (on track)
# R = rotate right
# O = noop
# X = reset
# C = repeat

sub expand_instructions($instrs) {
	return $instrs if $instrs !~ /X|C/;

	my %state = (E => 0, R => 0, A => 0);
	my $repeat_string = '';
	my $just_repeated = 0;
	my @rotation_resets = ('', 'r', 'rr', 'rrr', 'RR', 'R', '', 'r', 'rr', 'RRR', 'RR', 'R');

	for (my $pos = 0; $pos < length $instrs; ++$pos) {
		local $_ = chr vec($instrs, $pos, 8);
		next if $_ eq "\0";
		$state{uc $_} += ($_ eq uc ? 1 : -1);

		if ($_ eq 'C') {
			$just_repeated = 1;
			vec($instrs, $pos++, 8) = ord $& while $repeat_string =~ /./g;
			--$pos;
			%state = (E => 0, R => 0, A => 0);
			next;
		}

		if ($just_repeated) {
			$repeat_string = '';
			$just_repeated = 0;
		}

		if ($_ eq 'X') {
			my $reset_string = '';
			$reset_string .= 'g' if $state{G};
			$reset_string .= 'e' x  $state{E} if $state{E} > 0;
			$reset_string .= $rotation_resets[$state{R} // 0] // die "too much rotate: $state{R}";
			$reset_string .= 'a' x  $state{A} if $state{A} > 0;
			$reset_string .= 'A' x -$state{A} if $state{A} < 0;
			$reset_string .= 'E' x -$state{E} if $state{E} < 0;
			vec($instrs, $pos++, 8) = ord $& while $reset_string =~ /./g;
			--$pos;
			%state = (E => 0, R => 0, A => 0);
			$repeat_string .= $reset_string;
		} else {
			$repeat_string .= $_;
		}
	}

	return $instrs;
}

sub normalize($parts) {
	$_->{instructions} = expand_instructions($_->{instructions}) for @$parts;
	my $tape_length = tape_length(@$parts);
	@$parts = grep { $_->{part_name} ne 'glyph-marker' } @$parts;
	my @arms = grep { $_->{instructions} =~ /\w/ } @$parts;
	my $start_delay = min map { $_->{instructions} =~ /\w/; $-[0] } @arms;
	$_->{instructions} = substr($_->{instructions}, $start_delay) for @arms;

	for (5, 4, 3, 2) {
		next if $tape_length % $_;
		my $period = $tape_length / $_;
		next if any {
			my %h = map { s/\0+$//r => 1 } $_->{instructions} =~ /(?:^\0+)?\K.{1,$period}/g;
			keys %h > 1
		} @arms;
		$_->{instructions} =~ s/^\0*+.{$period}\K.*// for @arms;
		$tape_length = $period;
	}

	map { $_->{instructions} =~ s/O/\0/g; $_->{instructions} =~ s/\0+$// } @arms;

	my ($out) = grep { $_->{part_name} eq 'out-std' } @$parts;
	translate_parts($parts, -$out->{x}, -$out->{y});
	rotate_parts($parts, -$out->{rotation});

	@$parts = sort {
		$a->{part_name} cmp $b->{part_name} ||
		($a->{x} + $a->{y} / 2) <=> ($b->{x} + $b->{y} / 2) ||
		abs($a->{y}) <=> abs($b->{y}) ||
		uc($a->{instructions}) cmp uc($b->{instructions}) ||
		$a->{y} <=> $b->{y}
	} @$parts;

	my $new_tape_length = tape_length(@arms);
	if ($new_tape_length != $tape_length) {
		my $arm = first { $_->{instructions} =~ /\w/ } @$parts;
		$arm->{instructions} =~ /\w/;
		vec($arm->{instructions}, $-[0] + $tape_length - 1, 8) ||= ord 'O';
	}

	my $first = first { $_->{instructions} && $_->{y} } @$parts;
	mirror_parts($parts) if $first and $first->{y} < 0;

	for my $part (@$parts) {
		my $name = $part->{part_name};
		$part->{rotation} %= ($rotational_symmetry{$name} // 6);
		if (($name =~ /^(?:un)?bonder$/) && $part->{rotation} >= 3) {
			$part->{x} += $part->{rotation} - 4;
			$part->{y} -= $part->{rotation} > 3;
			$part->{rotation} %= 3;
		}
		if ($name eq 'track') {
			my ($xfx, $xfy, $yfx, $yfy) = $xy_rotations[$part->{rotation}]->@*;
			map {
				my ($x, $y) = @$_;
				$_->[0] = $x * $xfx + $y * $xfy;
				$_->[1] = $x * $yfx + $y * $yfy;
			} $part->{track}->@*;
			$part->{rotation} = 0;
			# TODO normalize loop start point
		}
	}
}

sub deep_copy(@parts) {
	return map {
		$_ = { %$_ };
		$_->{track} = [map [ @$_ ], $_->{track}->@*] if $_->{track};
		$_;
	} @parts;
}

sub tape_length(@parts) {
	return max map { $_->{instructions} =~ /\w.*/ ? $+[0] - $-[0] : 0 } @parts;
}

sub minify($parts) {
	my $old_name = $_->{part_name};
	return if $old_name =~ /^(?:input|out-std|glyph-marker)$/;

	my $old_instrs = $_->{instructions};
	$_->{part_name} = 'glyph-marker';
	$_->{instructions} = '';

	return 1 if omsim(@$parts);

	$_->{instructions} = $old_instrs;
	return 1 if $old_instrs =~ /\w/ and omsim(@$parts);

	if ($old_name =~ /^arm([236])$/ and $old_instrs !~ /R/i) {
		$_->{part_name} = 'arm1';
		for my $i (1..$1) {
			$_->{rotation} += 6 / $1;
			return 1 if omsim(@$parts);
		}
	}

	$_->{part_name} = $old_name;

	if ($_->{track} and $_->{track}->@* > 2) {
		my $track = $_->{track};
		my $segment = pop @$track;
		return 1 if omsim(@$parts);
		push @$track, $segment;
		$segment = shift @$track;
		return 1 if omsim(@$parts);
		unshift @$track, $segment;
	}

	return 0;
}

sub halvify(@parts) {
	my @inputs = grep { $_->{part_name} eq 'input' } @parts;
	die if @inputs == 0;
	return [ @parts ] if @inputs == 1;

	my @halves = ();
	for my $input (@inputs) {
		my $copy = [ deep_copy(grep { $_ != $input } @parts) ];
		if (omsim(@$copy)) {
			$_->{instructions} = expand_instructions($_->{instructions}) for @$copy;
			1 while any { minify($copy) } @$copy;
			push @halves, $copy;
		}
	}
	return @halves;
}

sub normalize_and_save($context, @parts) {
	state %known_bad = (
		swonL_bs9JyzdqmZ6LT1Og => 1,
		NTVk5zcKLZINbEQpBc_I0w => 1,
	);

	die "$context: trying to normalize broken solve" if not omsim(@parts);
	normalize(\@parts);
	my $solution = parts_to_solution(@parts);
	my $md5 = md5_base64($solution) =~ y(/)(_)r;
	return if $known_bad{$md5};
	write_file("normalized/$md5.solution", $solution, 1);
	die "$context => $md5 normalizing broke solve" if not omsim(@parts);
	normalize(\@parts);
	my $solution_new = parts_to_solution(@parts);
	my $md5_new = md5_base64($solution_new) =~ y(/)(_)r;
	write_file("normalized/$md5_new.solution", $solution_new, 1), die "$context: $md5 => $md5_new" if $md5_new ne $md5;
}

########
# Main #
########
if ($h) {
	say "-u: update solution list";
	say "-n: name solutions";
	say "-o: output sorted names";
	say "-g: generate halves";
	say "-m: merge halves";
	exit;
}

wget('https://zlbb.faendir.com/om/puzzle/P007/records?includeFrontier=true', 'data.json', $u);

my @solves = grep { !$_->{score}->{overlap} } @{ decode_json(slurp('data.json') =~ s(·|/∞r|@∞)()gr) };

my @nplets = map {
	my $nplet = parse_nplet($_->{score});
	my $file_name = nplet_to_filename(@$nplet);
	wget($_->{gif}, "gif/$file_name.gif") if $u;
	wget($_->{solution}, "solution/$file_name.solution") if $u;
	$nplet;
} @solves;

say 0+@nplets, " paretos";


if ($n) {
	open my $fh, '>', 'names.txt';
	say $fh "$solves[$_]{fullFormattedScore}: ", join ' ', name($nplets[$_], \@nplets) for 0..$#nplets;
}

if ($o) {
	my %names = ();
	open my $fh, '<', 'names.txt';
	while (<$fh>) {
		my ($key, $names) = /(.*?): (.*)/;
		my @names = split ' ', $names;
		@names = grep !is_superstring_of_any($_, @names), @names;
		@names = sort { compare_names($a, $b) } @names;
		$names{$key} = \@names;
	}

	for (sort { compare_names($names{$a}[0], $names{$b}[0]) } keys %names) {
		say "$_: ", join ', ', @{$names{$_}};
	}
}

sub omsim(@parts) {
	state ($out, $in, $err);
	BEGIN {
		open3($out, $in, $err, 'omsim/omsim');
		binmode $out;
	}
	print $out parts_to_solution(@parts);
	return <$in> =~ s([/\n])()gr;
}

sub add_repeats($part, $repeats) {
	my $instrs = $part->{instructions};
	return unless $instrs;
	$instrs =~ /\w/;
	my $delay = $-[0];
	vec($instrs, $delay + $_, 8) = 67 for @$repeats;
	$part->{instructions} = $instrs;
}

sub try_merge($repeats_a, $repeats_b, $half_a, @halves_b) {
	$half_a = [ deep_copy(@$half_a) ];
	add_repeats($_, $repeats_a) for @$half_a;

	for my $mirroring_done (0, 1) {

	my %map = ();
	$map{"$$_{x};$$_{y}"} = $$_{part_name} for @$half_a;

	HALF_B: for my $half_b (@halves_b) {
		my @merged = deep_copy(@$half_a);
		for (@$half_b) {
			next if $_->{part_name} eq "out-std";
			my $overlap = $map{"$$_{x};$$_{y}"};
			next if $overlap and $_->{part_name} eq "glyph-calcification" and $overlap eq "glyph-calcification";
			next HALF_B if $overlap;
			add_repeats($_, $repeats_b);
			push @merged, { %$_ };
		}

		my $pretty = omsim(@merged);
		if (!$pretty) {
			for (1..3) {
				for (@merged[@$half_a..$#merged]) {
					$_->{instructions} =~ s/^/\0/ if $_->{instructions};
				}
				$pretty = omsim(@merged);
				last if $pretty;
			}
		}
		next unless $pretty;

		next if -f "merged/$pretty.solution";
		my $nplet = [$pretty =~ /[\d.]+/g];
		my ($goodV, @tiesV) = is_pareto($nplet, 255, \@nplets);
		my ($goodINF, @tiesINF) = is_pareto($nplet, 3861, \@nplets);
		next unless ($goodV and @tiesV == 0) or ($goodINF and @tiesINF == 0);
		my @names = name($nplet, \@nplets);
		say "$pretty: ", join ', ', @names;
		write_file("merged/$pretty.solution", parts_to_solution(@merged), 1);
	}

	if (!$mirroring_done) {
		$half_a = [@$half_a];
		mirror_parts($half_a);
	}}
}

if ($g) {
	for my $file (<halves/*/*.solution>) {
		my @parts = solution_to_parts(slurp($file, 1));
		normalize_and_save($file, @parts);
	}

	for my $file (<solution/*.solution>) {
		my @parts = solution_to_parts(slurp($file, 1));
		normalize_and_save($file, @$_) for halvify(@parts);
	}
}

if ($m) {
	my @halves = map [solution_to_parts(slurp($_, 1))], <normalized/*.solution>;
	my @R4 = ();
	my @R5 = ();
	my @R6 = ();
	my @RR = ();
	for (@halves) {
		my $tape_length = tape_length(@$_);
		push @R4, $_ if $tape_length == 4;
		push @R5, $_ if $tape_length == 5;
		push @R6, $_ if $tape_length == 6;
		push @RR, $_ if $tape_length > 6;
	}

	try_merge([], [], $_, @halves) for @halves;

	try_merge([4, 8], [6], $_, @R6) for @R4;
	try_merge([6], [4, 8], $_, @R4) for @R6;
	try_merge([4, 8, 12], [5, 10], $_, @R5) for @R4;
	try_merge([5, 10], [4, 8, 12], $_, @R4) for @R5;
	try_merge([5, 10], [6, 12], $_, @R6) for @R5;
	try_merge([6, 12], [5, 10], $_, @R5) for @R6;
	try_merge([4], [], $_, @R6) for @R4;
	try_merge([], [4], $_, @R4) for @R6;
}

# my $test_filename = '/home/grimy/Games/solutions/test.solution';
# my @test_parts = solution_to_parts(slurp($test_filename, 1));
# normalize(\@test_parts);
# write_file($test_filename, parts_to_solution(@test_parts), 1);

# for my $file (<halves/R6/face-powder-39.solution>) {
	# my @parts = solution_to_parts(slurp($file, 1));
	# say join ' ', map { $_->{instructions } } @parts;
	# normalize(\@parts);
	# say join ' ', map { $_->{instructions } } @parts;
	# normalize(\@parts);
	# say join ' ', map { $_->{instructions } } @parts;
	# normalize(\@parts);
	# say join ' ', map { $_->{instructions } } @parts;
# }

# for my $file (<solution/170g19c22a18i5h4w2r.solution>) {
	# my @parts = solution_to_parts(slurp($file, 1));
	# normalize_and_save($file, @$_) for halvify(@parts);
# }

# for my $file (<normalized/*.solution>) {
	# my @parts = solution_to_parts(slurp($file, 1));
	# my $nplet = omsim(@parts);
	# $_->{instructions} = '' for @parts;
	# my $solution = parts_to_solution(@parts);
	# my $md5 = md5_base64($solution) =~ y(/)(_)r;
	# say "$md5 $nplet $file";
# }

# TODO: how are those two different?
# normalized/1PfjJr5qpoUYcu_COyjFyw.solution
# normalized/HnOe_b4uAvgHIoT0sw40RA.solution
