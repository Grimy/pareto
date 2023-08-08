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
		next if any { ($_ & ~$mask) == 0 } @good_masks;
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

			my $dx = $track[-1][0] - $track[0][0];
			my $dy = $track[-1][1] - $track[0][1];
			$result->{loops} = @track > 2 && abs($dx) <= 1 && abs($dy) <= 1 && abs($dx + $dy) <= 1;
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

sub expand_instructions(@parts) {
	for my $part (@parts) {
		my $instrs = $part->{instructions};
		next if $instrs !~ /X|C/;

		my %state = (E => 0, R => 0, A => 0);
		my $repeat_start = 0;
		my $repeat_end = -1;
		my $just_repeated = 1;
		my $trackloop = 0;

		if ($instrs =~ /a/i) {
			my $point = [ $part->{x}, $part->{y} ];
			my $track = first { $_->{track} and any { point_eq($_, $point) } $_->{track}->@* } @parts;
			$trackloop = $track->{loops} ? $track->{track}->@* : 9999;
		}

		for (my $pos = 0; $pos < length $instrs; ++$pos) {
			local $_ = chr vec($instrs, $pos, 8);
			next if $_ eq "\0";
			$state{uc $_} += ($_ eq uc ? 1 : -1);

			if ($_ eq 'C') {
				$just_repeated = 1;
				vec($instrs, $pos++, 8) = vec($instrs, $_, 8) for $repeat_start..$repeat_end;
				--$pos;
				%state = (E => 0, R => 0, A => 0);
				next;
			}

			$repeat_start = $pos if $just_repeated;

			if ($_ eq 'X') {
				my $reset_string = '';
				$reset_string .= 'g' if $state{G};
				$reset_string .= 'e' x  $state{E} if $state{E} > 0;
				if ($state{R}) {
					my $bias = (6 - ($state{R} > 0)) >> 1;
					my $amount = ($state{R} + $bias) % 6 - $bias;
					$reset_string .= $amount > 0 ? 'r' x $amount : 'R' x -$amount;
				}
				if ($state{A}) {
					my $bias = ($trackloop - ($state{A} > 0)) >> 1;
					my $amount = ($state{A} + $bias) % $trackloop - $bias;
					$reset_string .= $amount > 0 ? 'a' x $amount : 'A' x -$amount;
				}
				$reset_string .= 'E' x -$state{E} if $state{E} < 0;
				vec($instrs, $pos++, 8) = ord $& while $reset_string =~ /./g;
				--$pos;
				%state = (E => 0, R => 0, A => 0);
			}

			$repeat_end = $pos;
			$just_repeated = 0;
		}

		$part->{instructions} = $instrs;
	}
}

sub normalize($parts) {
	expand_instructions(@$parts);
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
			my %points = ();
			map {
				my ($x, $y) = @$_;
				$_->[0] = $x * $xfx + $y * $xfy;
				$_->[1] = $x * $yfx + $y * $yfy;
				++$points{"@$_"};
			} $part->{track}->@*;

			my @arms_on_track = grep { $points{"@$_{qw(x y)}"} } @arms;
			if (0 < sum map { $_->{instructions} =~ /a/i ? (ord($&) - 81) * 2**-$-[0] : 0 } @arms_on_track) {
				$_->{instructions} =~ y/Aa/aA/ for @arms_on_track;
				$part->{track} = [reverse $part->{track}->@*];
			}

			# TODO normalize loop start point

			($part->{x}, $part->{y}) = $part->{track}->[0]->@*;
			$part->{rotation} = 0;
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

sub omsim(@parts) {
	state ($out, $in, $err);
	BEGIN {
		open3($out, $in, $err, 'omsim/omsim');
		binmode $out;
	}
	print $out parts_to_solution(@parts);
	return <$in> =~ s([/\n])()gr;
}

sub minify($parts, $initial_score) {
	my $old_name = $_->{part_name};
	return if $old_name =~ /^(?:input|out-std|glyph-marker)$/;

	my $old_instrs = $_->{instructions};
	$_->{part_name} = 'glyph-marker';
	$_->{instructions} = '';

	sub cycles($str) { $str =~ /\d+(?=c)/ ? $& : 99999; }

	return 1 if cycles(omsim(@$parts)) <= cycles($initial_score);

	# TODO handle this without omsim modifications
	$_->{instructions} = $old_instrs;
	return 1 if $old_instrs =~ /\w/ and cycles(omsim(@$parts)) <= cycles($initial_score);

	if ($old_name =~ /^arm([236])$/ and $old_instrs !~ /R/i) {
		$_->{part_name} = 'arm1';
		for my $i (1..$1) {
			$_->{rotation} += 6 / $1;
			return 1 if cycles(omsim(@$parts)) <= cycles($initial_score);
		}
	}

	$_->{part_name} = $old_name;

	if ($_->{track} and $_->{track}->@* > 2 and !$_->{loops}) {
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
		my $score = omsim(@$copy);
		if ($score) {
			expand_instructions(@$copy);
			1 while any { minify($copy, $score) } @$copy;
			push @halves, $copy;
		}
	}
	return @halves;
}

sub add_repeats($parts, $period) {
	for (@$parts) {
		next unless $_->{instructions} =~ /\w/;
		vec($_->{instructions}, $-[0] + $period, 8) = ord 'C';
	}
}

sub part_points($part) {
	return $part->{track}->@* if $part->{part_name} eq 'track';
	my @result = [$part->{x}, $part->{y}];

	if ($part->{part_name} =~ /^(?:out-std|bonder|debonder|bonder-speed)$/) {
		my ($xfx, $xfy, $yfx, $yfy) = @{$xy_rotations[$part->{rotation} % 6]};
		push @result, [$part->{x} + $xfx, $part->{y} + $yfx];
		if ($part->{part_name} eq 'bonder-speed') {
			push @result, [$part->{x} - $xfx + $xfy, $part->{y} + - $yfx + $yfy];
			push @result, [$part->{x} - $xfy, $part->{y} - $yfy];
		}
	}

	@result;
}

sub point_eq($a, $b) {
	return $a->[0] == $b->[0] && $a->[1] == $b->[1];
}

sub merge_tracks($a, $b) {
	my @a = $a->{track}->@*;
	my @b = $b->{track}->@*;
	my @pre = ();
	my @post = ();
	my $target = \@pre;

	for my $bi (0..$#b) {
		my $ai = first { point_eq($a[$_], $b[$bi]) } 0..$#a;
		if (defined($ai)) {
			return if $ai > 0 && $bi > 0 && !point_eq($a[$ai - 1], $b[$bi - 1]);
			return if $ai < $#a && $bi < $#b && !point_eq($a[$ai + 1], $b[$bi + 1]);
			$target = \@post;
		} else {
			push @$target, $b[$bi];
		}
	}

	$a->{track} = [@pre, @a, @post];
	$b->{deleted} = 1;
	# TODO handle loops
}

sub handle_overlap($a, $b, %map) {
	return 1 if $a->{deleted};
	my ($a_name, $b_name) = ($a->{part_name}, $b->{part_name});
	my ($a_is_track, $a_is_arm) = ($a_name eq 'track', $a_name =~ /^(?:arm[1236]|piston)$/);
	my ($b_is_track, $b_is_arm) = ($b_name eq 'track', $b_name =~ /^(?:arm[1236]|piston)$/);

	if ($a_is_track && $b_is_track) {
		return 1 if merge_tracks($a, $b);
		my @arms_on_b = grep { $_->{instructions} } map { @$_ } @map{map { "@$_" } $b->{track}->@*};
		$_->{instructions} =~ y/Aa/aA/ for @arms_on_b;
		$b->{track} = [reverse $b->{track}->@*];
		return merge_tracks($a, $b);
	}

	elsif ($a_is_arm && $b_is_arm) {
		return if $a->{size} != $b->{size};
		return if $a->{instructions} ne $b->{instructions};
		my $handles = 1;
		my $dr = $b->{rotation} - $a->{rotation};
		$handles *= 2 if $a_name =~ /^arm[26]$/ or $b_name =~ /^arm[26]$/ or $dr % 2;
		$handles *= 3 if $a_name =~ /^arm[36]$/ or $b_name =~ /^arm[36]$/ or $dr % 3;
		if ($a_name eq 'piston' or $b_name eq 'piston') {
			return if $handles > 1;
		} else {
			$a->{part_name} = "arm$handles";
		}
		$b->{deleted} = 1;
	}

	else {
		return 1 if ($a_is_track && $b_is_arm) || ($a_is_arm && $b_is_track);
		return if $a_name ne $b_name;
		return if $a->{rotation} != $b->{rotation};
		return if $a->{x} != $b->{x} || $a->{y} != $b->{y};
		$b->{deleted} = 1;
		# TODO bonder+bonder => bonder-speed?
		# TODO bonder+bonder-speed => delete bonder?
	}

	return 1;
}

sub deoverlap($parts) {
	my %map = ();
	for my $part (@$parts) {
		for my $point (part_points($part)) {
			my $overlaps = ($map{"@$point"} //= []);
			return if any { !handle_overlap($part, $_, %map) } @$overlaps;
			push @$overlaps, $part;
		}
	}
	@$parts = grep { !$_->{deleted} } @$parts;
	return 1;
}

sub try_merge($half_a, $half_b) {
	my @reference = deep_copy(@$half_a, @$half_b);

	for (0..3) {
		if ($_) {
			$_->{instructions} =~ s/(?=\w)/\0/ for @reference[@$half_a..$#reference];
		}
		my @merged = deep_copy(@reference);
		next unless deoverlap(\@merged);
		my $pretty = omsim(@merged);
		return [@merged, $pretty] if $pretty;
	}

	return;
}

sub try_all_merges($a, $b) {
	my $ola = tape_length(@$a);
	my $olb = tape_length(@$b);
	my ($la, $lb) = ($ola, $olb);

	my @results = try_merge($a, $b);
	return @results if $la == $lb;

	$a = [ deep_copy(@$a) ];
	$b = [ deep_copy(@$b) ];

	for (1..6) {
		if ($la < $lb) {
			add_repeats($a, $la);
			$la += $ola;
		} elsif ($la > $lb) {
			add_repeats($b, $lb);
			$lb += $olb;
		}
		push @results, try_merge($a, $b);
		last if $la == $lb;
	}

	return @results;
}

sub save_and_check(@parts) {
	state %known_bad = (
		swonL_bs9JyzdqmZ6LT1Og => 1,
		NTVk5zcKLZINbEQpBc_I0w => 1,
	);

	my $solution = parts_to_solution(@parts);
	my $md5 = md5_base64($solution) =~ y(/)(_)r;
	return if $known_bad{$md5};
	# return if -f "normalized/$md5.solution";
	write_file("normalized/$md5.solution", $solution, 1);

	normalize(\@parts);
	die "normalizing broke solve: $md5" if not omsim(@parts);
	my $solution_new = parts_to_solution(@parts);
	my $md5_new = md5_base64($solution_new) =~ y(/)(_)r;
	if ($md5_new ne $md5) {
		write_file("test/$md5_new.solution", $solution_new, 1);
		die "non-idempotent normalization: $md5 => $md5_new";
	}
}

sub save_if_pareto($context, $solve) {
	my $pretty = pop @$solve;
	my $nplet = [$pretty =~ /[\d.]+/g];
	my ($goodV, @tiesV) = is_pareto($nplet, 255, $context);
	my ($goodINF, @tiesINF) = is_pareto($nplet, 3861, $context);
	# say $pretty if $goodV or $goodINF;
	return unless ($goodV and @tiesV == 0) or ($goodINF and @tiesINF == 0);
	my @names = name($nplet, $context);
	say "$pretty: ", join ', ', @names;
	write_file("merged/$pretty.solution", parts_to_solution(@$solve), 1);
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
		@names = grep { my $this = $_; any { is_substring($_, $this) } @names } @names;
		@names = sort { compare_names($a, $b) } @names;
		$names{$key} = \@names;
	}

	for (sort { compare_names($names{$a}[0], $names{$b}[0]) } keys %names) {
		say "$_: ", join ', ', @{$names{$_}};
	}
}

if ($g) {
	my %halves = ();

	for my $file (<{solution,extra_solutions}/*.solution>) {
		my @parts = solution_to_parts(slurp($file, 1));
		my $goal = omsim(@parts);
		my @inputs = grep { $_->{part_name} eq 'input' } @parts;
		my @halves = halvify(@parts);

		normalize($_) for @halves;
		save_and_check(@$_) for @halves;

		if (@inputs == 1) {
			die if @halves != 1;
			my $attempt = omsim($halves[0]->@*);
			die "$attempt ne $goal" if $attempt ne $goal;
		}
		elsif (@halves == 2) {
			my @attempts = try_all_merges($halves[0], $halves[1]);
			push @attempts, try_all_merges($halves[1], $halves[0]);
			mirror_parts($halves[0]);
			push @attempts, try_all_merges($halves[0], $halves[1]);
			push @attempts, try_all_merges($halves[1], $halves[0]);
			mirror_parts($halves[0]);
			if (!any { $_->[-1] eq $goal } @attempts) {
				say "attempts = ", 0+@attempts;
				say $_->[-1] for @attempts;
				say md5_base64(parts_to_solution(@$_)) =~ y(/)(_)r for @halves;
				die $file;
			}
		}
	}
}

if ($m) {
	my @halves = map [solution_to_parts(slurp($_, 1))], <normalized/*.solution>;

	for (0..$#halves) {
		my $a = $halves[$_];
		save_if_pareto(\@nplets, $_) for map { try_all_merges($_, $a) } @halves[$_..$#halves];
		mirror_parts($a);
		save_if_pareto(\@nplets, $_) for map { try_all_merges($_, $a) } @halves[$_..$#halves];
	}
}

# my @halves = map [ solution_to_parts(slurp($_, 1)) ], <test{1,2}.solution>;
# normalize $_ for @halves;
# mirror_parts($halves[0]);
# try_all_merges([], $halves[1], $halves[0]);
# try_all_merges([], $halves[0], $halves[1]);

# for my $file (<solution/*g15c*.solution>) {
	# my @parts = solution_to_parts(slurp($file, 1));
	# for (halvify(@parts)) {
		# normalize($_);
		# say $file, " => ", md5_base64(parts_to_solution(@$_)) =~ y(/)(_)r;
	# }
# }

# for my $file (<{solution/195g16c21a24i6h4w2r.solution,solution/210g17c24a22i5h4w2r.solution}>) {
	# my @parts = solution_to_parts(slurp($file, 1));
	# ($_) = halvify(@parts);
	# say md5_base64(parts_to_solution(@$_)) =~ y(/)(_)r;
	# normalize($_);
	# say Dumper $_->[-1];
	# say md5_base64(parts_to_solution(@$_)) =~ y(/)(_)r;
# }

# for my $file (<solution/195g16c21a24i6h4w2r.solution>) {
	# my @parts = solution_to_parts(slurp($file, 1));
	# for (halvify(@parts)) {
		# normalize($_);
		# say md5_base64(parts_to_solution(@$_)) =~ y(/)(_)r;
	# }
# }

# for my $file (<normalized/*.solution>) {
	# my @parts = solution_to_parts(slurp($file, 1));
	# my $nplet = omsim(@parts);
	# $_->{instructions} = '' for @parts;
	# my $solution = parts_to_solution(@parts);
	# my $md5 = md5_base64($solution) =~ y(/)(_)r;
	# say "$md5 $nplet $file";
# }
