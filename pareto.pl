#!/bin/perl -s

use utf8;
use v5.36;
use warnings;
use Data::Dumper;
use Digest::MD5 qw(md5_base64);
use IPC::Open3;
use JSON qw(decode_json);
use List::Util qw(min max any all sum product first uniq);
use Memoize;


our ($h, $u, $n, $g, $m, $v);

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
	return grep { ($mask >> $_) & 1 } 0..11;
}

sub mask_to_letters($mask) {
	my @letters = qw(T C G A I H W L R A H W)[mask_to_list($mask)];
	local $" = '';
	return $#letters ? "(@letters)" : "@letters";
}

my $MASK_V = 255;
my $MASK_INF = 3861;

sub get_masks() {
	return sort {
		mask_to_list($a) <=> mask_to_list($b) ||
		$a <=> $b
	} grep {
		!(($_ & ~$MASK_V) && ($_ & ~$MASK_INF)) &&
		!(($_ & 129) && ($_ & ($_ - 1)))
	} 1..4095;
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

sub count_outparetos($this, $mask, $context) {
	my @metrics = mask_to_list($mask);
	my $result = 0;
	for my $that (@$context) {
		++$result if all { $that->[$_] <= $this->[$_] } @metrics;
	}
	return $result;
}

sub get_suffix($nplet, $mask, $context) {
	return '' if ($mask & ($mask - 1)) == 0;
	my @metrics = mask_to_list($mask);
	my $sum = sum @$nplet[@metrics];
	my $product = product @$nplet[@metrics];
	return '⁺' if all { $sum <= sum @$_[@metrics] } @$context;
	return 'ˣ' if all { $product <= product @$_[@metrics] } @$context;
}

sub name_impl($nplet, $context, $ban_mask) {
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
			push @good_names, "$letters$_" for name_impl($nplet, \@ties, $ban_mask | $mask | $future_ban_mask);
		}
	}

	return @good_names;
}

sub name($nplet, $context) {
	my @names = name_impl($nplet, $context, ~$MASK_V);
	# TODO more clever @V <=> @INF prioritization
	# @names = name($nplet, $context, ~$MASK_INF) if !@names;
	push @names, name_impl($nplet, $context, ~$MASK_INF);
	@names = grep { my $this = $_; !any { is_substring($_, $this) } @names } @names;
	@names = sort { compare_names($a, $b) } @names;
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
			$result->{loops} = 1 if @track > 2 && abs($dx) <= 1 && abs($dy) <= 1 && abs($dx + $dy) <= 1;
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
	[ 0,  1, -1,  1],
	[-1,  1, -1,  0],
	[-1,  0,  0, -1],
	[ 0, -1,  1, -1],
	[ 1, -1,  1,  0],
);

sub rotate_parts($parts, $rotation) {
	my ($xfx, $yfx, $xfy, $yfy) = $xy_rotations[$rotation]->@*;
	for my $part (@$parts) {
		$part->{rotation} += $rotation;
		my ($x, $y) = ($part->{x}, $part->{y});
		$part->{x} = $x * $xfx + $y * $xfy;
		$part->{y} = $x * $yfx + $y * $yfy;
	}
}

sub rotation_from_point($dx, $dy) {
	return first { point_eq($xy_rotations[$_], [$dx, $dy]) } 0..5;
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

		if ($instrs =~ /A/i) {
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

sub tape_length(@parts) {
	return max map { $_->{instructions} =~ /\w.*/ ? $+[0] - $-[0] : 0 } @parts;
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
			$part->{x} += $xy_rotations[$part->{rotation}][0];
			$part->{y} += $xy_rotations[$part->{rotation}][1];
			$part->{rotation} %= 3;
		}

		if ($name eq 'track') {
			my $track = $part->{track};
			my ($xfx, $yfx, $xfy, $yfy) = $xy_rotations[$part->{rotation}]->@*;
			map {
				my ($x, $y) = @$_;
				$_->[0] = $x * $xfx + $y * $xfy;
				$_->[1] = $x * $yfx + $y * $yfy;
			} @$track;

			my %points = map { ("@$_" => 1) } @$track;
			my @arms_on_track = grep { $points{"@$_{qw(x y)}"} } @arms;
			if (0 < sum map { $_->{instructions} =~ /A/i ? (ord($&) - 81) * 2**-$-[0] : 0 } @arms_on_track) {
				$_->{instructions} =~ y/Aa/aA/ for @arms_on_track;
				@$track = reverse @$track;
			}

			# TODO normalize loop start point
			@$part{qw(x y)} = $track->[0]->@*;
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
		my ($xfx, $yfx, $xfy, $yfy) = $xy_rotations[$part->{rotation} % 6]->@*;
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

	if ($a_is_arm && $b_is_arm) {
		return if $a->{size} != $b->{size};
		return if $a->{instructions} ne $b->{instructions};
		my $grippers = 1;
		my $dr = $b->{rotation} - $a->{rotation};
		$grippers *= 2 if $a_name =~ /^arm[26]$/ or $b_name =~ /^arm[26]$/ or $dr % 2;
		$grippers *= 3 if $a_name =~ /^arm[36]$/ or $b_name =~ /^arm[36]$/ or $dr % 3;
		if ($a_name eq 'piston' or $b_name eq 'piston') {
			return if $grippers > 1;
		} else {
			$a->{part_name} = "arm$grippers";
		}
		return $b->{deleted} = 1;
	}

	return 1 if ($a_is_track && $b_is_arm) || ($a_is_arm && $b_is_track);
	return if $a_name ne $b_name;
	return if $a->{rotation} != $b->{rotation};
	return if $a->{x} != $b->{x} || $a->{y} != $b->{y};
	# TODO bonder+bonder => bonder-speed?
	# TODO bonder+bonder-speed => delete bonder?
	return $b->{deleted} = 1;
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
	my @merged = deep_copy(@$half_a, @$half_b);
	my $pretty = omsim(@merged) if deoverlap(\@merged);
	return [@merged, $pretty] if $pretty;

	my @result = ();
	my @delayed = deep_copy(@$half_a);

	for (1..3) {
		$_->{instructions} =~ s/(?=\w)/\0/ for @delayed;
		@merged = deep_copy(@delayed, @$half_b);
		next unless deoverlap(\@merged);
		$pretty = omsim(@merged);
		if ($pretty) {
			push @result, [@merged, $pretty];
			last;
		}
	}

	@delayed = deep_copy(@$half_b);

	for (1..3) {
		$_->{instructions} =~ s/(?=\w)/\0/ for @delayed;
		@merged = deep_copy(@$half_a, @delayed);
		next unless deoverlap(\@merged);
		$pretty = omsim(@merged);
		if ($pretty) {
			push @result, [@merged, $pretty];
			last;
		}
	}

	return @result;
}

# TODO use better variable names here
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
	);

	my $solution = parts_to_solution(@parts);
	my $md5 = md5_base64($solution) =~ y(/)(_)r;
	say $md5, return if $known_bad{$md5};
	return $md5 if -f "normalized/$md5.solution";
	write_file("normalized/$md5.solution", $solution, 1);

	normalize(\@parts);
	die "normalizing broke solve: $md5" if not omsim(@parts);
	my $solution_new = parts_to_solution(@parts);
	my $md5_new = md5_base64($solution_new) =~ y(/)(_)r;
	if ($md5_new ne $md5) {
		write_file("test/$md5_new.solution", $solution_new, 1);
		die "non-idempotent normalization: $md5 => $md5_new";
	}
	return $md5;
}

sub fold_tracked_arms($parts) {
	my @arms = grep { $_->{instructions} =~ /\w/ } @$parts;
	for (@$parts) {
		next unless $_->{part_name} eq 'track';
		my %points = map { ("@$_" => 1) } $_->{track}->@*;
		my @arms_on_track = grep { $points{"@$_{qw(x y)}"} } @arms;
		next if @arms_on_track != 1;
		$arms_on_track[0]->{track} = $_->{track};
		$_->{deleted} = 1;
	}
	@$parts = grep { !$_->{deleted} } @$parts;
}

sub unfold_tracked_arms($parts) {
	for (@$parts) {
		next unless $_->{track} && $_->{part_name} ne 'track';
		push @$parts, {
			part_name => 'track',
			x => $_->{x},
			y => $_->{y},
			size => 1,
			rotation => 0,
			instructions => '',
			track => $_->{track},
		};
		delete $_->{track};
	}
}

sub arm1_for_move($grab_x, $grab_y, $dx, $dy, $clockwise, $instructions) {
	my $rotation = rotation_from_point(-$dx, -$dy);
	$rotation = $rotation + ($clockwise ? -1 : 1);
	my ($xfx, $yfx) = $xy_rotations[$rotation % 6]->@*;
	return {
		part_name => 'arm1',
		x => $grab_x - $xfx,
		y => $grab_y - $yfx,
		size => 1,
		rotation => $rotation,
		instructions => $instructions,
	}
}

sub part_variants($part) {
	my ($name, $x, $y, $size, $rotation, $instructions, $track) =
		@$part{qw(part_name x y size rotation instructions track)};

	my @active_instrs = $instructions =~ /G([^g]+)g/g;
	return if uniq(@active_instrs) != 1;
	my $active_instrs = $active_instrs[0];

	my ($xfx, $yfx) = $xy_rotations[$rotation]->@*;
	my $grab_x = $x + $size * $xfx;
	my $grab_y = $y + $size * $yfx;

	my @variants = ();

	if ($track) {
		return if $active_instrs =~ /[ER]/i;
		return if @$track > 3;
		my $dx = $$track[1][0] - $$track[0][0];
		my $dy = $$track[1][1] - $$track[0][1];
		return if $$track[2] && $$track[2][0] - $$track[1][0] != $dx;
		return if $$track[2] && $$track[2][1] - $$track[1][1] != $dy;

		my $rotation = rotation_from_point($dx, $dy);
		my ($xfx, $yfx) = $xy_rotations[$rotation]->@*;

		for my $size (1 .. 4-@$track) {
			push @variants, {
				part_name => 'piston',
				x => $grab_x - $size * $xfx,
				y => $grab_y - $size * $yfx,
				size => $size,
				rotation => $rotation,
				instructions => $instructions =~ y/Aa/Ee/r,
			};
		}
		for my $size (@$track .. 3) {
			push @variants, {
				part_name => 'piston',
				x => $grab_x + $size * $xfx,
				y => $grab_y + $size * $yfx,
				size => $size,
				rotation => $rotation + 3,
				instructions => $instructions =~ y/Aa/eE/r,
			};
		}

		if (@$track == 2) {
			push @variants, arm1_for_move($grab_x, $grab_y, $dx, $dy, 1, $instructions =~ y/Aa/Rr/r);
			push @variants, arm1_for_move($grab_x, $grab_y, $dx, $dy, 0, $instructions =~ y/Aa/rR/r);
		}
	}

	if ($name eq 'piston' and $active_instrs !~ /[AR]/i) {
		my $long = $active_instrs =~ /E[^e]*E|e[^E]*e/;
		my $push = $active_instrs =~ /^[^e]*E/;
		my $dx = $push ? $xfx : -$xfx;
		my $dy = $push ? $yfx : -$yfx;

		for my $rotation (0..5) {
			my ($xfx, $yfx) = $xy_rotations[$rotation]->@*;
			for my $size (1..3) {
				my $x = $grab_x - $size * $xfx;
				my $y = $grab_y - $size * $yfx;
				push @variants, {
					part_name => 'arm1',
					x => $x,
					y => $y,
					size => $size,
					rotation => $rotation,
					instructions => $push ? ($instructions =~ y/Ee/Aa/r) : ($instructions =~ y/Ee/aA/r),
					track => [map { [$x + $_ * $dx, $y + $_ * $dy] } 0 .. ($long ? 2 : 1)],
				}
			}
		}

		if (!$long) {
			push @variants, arm1_for_move($grab_x, $grab_y, $dx, $dy,  $push, $instructions =~ y/Ee/Rr/r);
			push @variants, arm1_for_move($grab_x, $grab_y, $dx, $dy, !$push, $instructions =~ y/Ee/rR/r);
		}
	}

	if ($name =~ /^arm([236])$/ and $active_instrs !~ /A/i) {
		push @variants, map {{
			part_name => 'arm1',
			x => $x,
			y => $y,
			size => $size,
			rotation => $rotation + $_ * (6 / $1),
			instructions => $instructions =~ y/g/X/r,
		}} 1..$1;
	}

	if ($name eq 'arm1' and $active_instrs =~ /R/i) {
		my $dr = ($active_instrs =~ y/R//) - ($active_instrs =~ y/r//);
		my $grippers = ($dr % 2 ? 2 : 1) * ($dr % 3 ? 3 : 1);
		if ($grippers != 1) {
			# TODO version without noops?
			push @variants, {
				part_name => "arm$grippers",
				x => $x,
				y => $y,
				size => $size,
				rotation => $rotation,
				instructions => $instructions =~ s(g\K[^gG]*)($&=~y/Rr/OO/r)erg,
			}
		}
	}

	if ($name eq 'arm1' and $active_instrs =~ /^P$/i) {
		for my $rotation (0..5) {
			my ($xfx, $yfx) = $xy_rotations[$rotation]->@*;
			for my $size (1..3) {
				push @variants, {
					part_name => 'arm1',
					x => $grab_x - $size * $xfx,
					y => $grab_y - $size * $yfx,
					size => $size,
					rotation => $rotation,
					instructions => $instructions,
				}
			}
		}
	}

	if ($name eq 'arm1' and $size == 1 and $active_instrs =~ /^[Pp]*[Rr][Pp]*$/) {
		my $clockwise = $active_instrs =~ /^[^r]*R/;
		my $normed_instrs = $clockwise ? $instructions : ($instructions =~ y/Rr/rR/r);
		my $movement_rotation = $rotation + ($clockwise ? -2 : 2);
		my ($dx, $dy) = $xy_rotations[$movement_rotation % 6]->@*;

		# TODO 2-rotate arm => RE/eR piston or bent 3-track

		for my $size (1..2) {
			push @variants, {
				part_name => 'piston',
				x => $grab_x - $size * $dx,
				y => $grab_y - $size * $dy,
				size => $size,
				rotation => $movement_rotation,
				instructions => $normed_instrs =~ y/Rr/Ee/r,
			};
		}
		for my $size (2..3) {
			push @variants, {
				part_name => 'piston',
				x => $grab_x + $size * $dx,
				y => $grab_y + $size * $dy,
				size => $size,
				rotation => $movement_rotation + 3,
				instructions => $normed_instrs =~ y/Rr/eE/r,
			};
		}

		for my $rotation (0..5) {
			my ($xfx, $yfx) = $xy_rotations[$rotation]->@*;
			for my $size (1..3) {
				my $x = $grab_x - $size * $xfx;
				my $y = $grab_y - $size * $yfx;
				push @variants, {
					part_name => 'arm1',
					x => $x,
					y => $y,
					size => $size,
					rotation => $rotation,
					instructions => $normed_instrs =~ y/Rr/Aa/r,
					track => [[$x, $y], [$x + $dx, $y + $dy]],
				}
			}
		}
	}

	if ($active_instrs =~ /^R$/i) {
		my $clockwise = $active_instrs eq 'R';
		my $end_rotation = $rotation + ($clockwise ? -1 : 1);
		my ($xfx, $yfx) = $xy_rotations[$end_rotation % 6]->@*;
		push @variants, {
			part_name => $name,
			x => $grab_x + $size * $xfx,
			y => $grab_y + $size * $yfx,
			size => $size,
			rotation => $end_rotation + 3,
			instructions => $instructions =~ y/Rr/rR/r,
		}
	}

	return @variants;
}

sub variantify(@parts) {
	@parts = deep_copy(@parts);
	normalize(\@parts);
	fold_tracked_arms(\@parts);
	my @variants = ();

	for my $i (0..$#parts) {
		for my $part_variant (part_variants($parts[$i])) {
			my @variant = deep_copy(@parts);
			$variant[$i] = $part_variant;
			unfold_tracked_arms(\@variant);
			next unless deoverlap(\@variant);
			my $pretty = omsim(@variant);
			push @variants, [@variant, $pretty] if $pretty;
			# push @variants, [@variant, "fail"] if !$pretty;
		}
	}

	return @variants;
}

########
# Main #
########
if ($h) {
	say "-u: update solution list";
	say "-n: name solutions";
	say "-g: generate halves";
	say "-m: merge halves";
	say "-v: variantify";
	exit;
}

wget('https://zlbb.faendir.com/om/puzzle/P007/records?includeFrontier=true', 'data.json', $u);

my @solves = grep { !$_->{score}->{overlap} } decode_json(slurp('data.json') =~ s(·|/∞r|@∞)()gr)->@*;

my %good = ();

my @nplets = map {
	my $nplet = parse_nplet($_->{score});
	my $file_name = nplet_to_filename(@$nplet);
	$good{"solution/$file_name.solution"} = 1;
	wget($_->{solution}, "solution/$file_name.solution") if $u;
	$nplet;
} @solves;

warn 0+@nplets, " paretos";

# for my $file (<solution/*.solution>) {
	# say $file if !$good{$file};
# }

# TODO go back to 8-plets, 9-plets tops
# say nplet_to_filename(@$_) for
	# sort { $$a[8] <=> $$b[8] }
	# grep {
		# ($$_[9] != 99999 and $$_[9] != $$_[3]) or
		# ($$_[10] != 99999 and $$_[10] != $$_[5]) or
		# ($$_[11] != 99999 and $$_[11] != $$_[6]);
	# } @nplets;

if ($n) {
	$solves[$_]{names} = [name($nplets[$_], \@nplets)] for 0..$#nplets;
	# for (sort { compare_names($$a{names}[0], $$b{names}[0]) } @solves) {
		# say "$$_{fullFormattedScore}: @{$$_{names}}";
	# }
	for (sort { $$a{lastModified} cmp $$b{lastModified} } grep { $$_{lastModified} } @solves) {
		say "$$_{fullFormattedScore}: @{$$_{names}}";
	}
}

if ($g) {
	my %old_md5 = map { /\/(.*?)\./; $1 => 1 } <normalized/*.solution>;
	my %new_md5 = ();

	for my $file (<{solution,extra_solutions}/*.solution>) {
		my @parts = solution_to_parts(slurp($file, 1));
		my $goal = omsim(@parts);
		my @inputs = grep { $_->{part_name} eq 'input' } @parts;
		my @halves = halvify(@parts);

		normalize($_) for @halves;
		++$new_md5{$_} for map { save_and_check(@$_) } @halves;

		if (@inputs == 1) {
			die if @halves != 1;
			my $attempt = omsim($halves[0]->@*);
			die "$attempt ne $goal" if $attempt ne $goal;
		}
		elsif (@halves == 2) {
			my @attempts = try_all_merges($halves[0], $halves[1]);
			mirror_parts($halves[0]);
			push @attempts, try_all_merges($halves[0], $halves[1]);
			mirror_parts($halves[0]);
			@attempts = map { $_->[-1] } @attempts;
			die join "\n", $goal, @attempts if !any { $_ eq $goal } @attempts;
		}
	}

	warn "new md5: $_" for grep { !$old_md5{$_} } keys %new_md5;
	warn "old md5: $_" for grep { !$new_md5{$_} } keys %old_md5;
}

if ($v) {
	my %known = ();
	my @q = ([]);
	my @halves = map [solution_to_parts(slurp($_, 1))], <normalized/*.solution>;

	sub postprocess($parts) {
		my $pretty = pop @$parts;
		normalize($parts);
		my $solution = parts_to_solution(@$parts);
		my $md5 = md5_base64(parts_to_solution(@$parts)) =~ y(/)(_)r;
		return if $known{$md5}++;
		my $nplet = [$pretty =~ /[\d.]+/g];
		my $outV = count_outparetos($nplet, $MASK_V, \@nplets);
		my $outINF = count_outparetos($nplet, $MASK_INF, \@nplets);
		my $true_outs = min($outV, $outINF);
		push $q[$true_outs]->@*, $parts if $true_outs < 32;
		return if $true_outs;
		my @names = name($nplet, \@nplets);
		say "$pretty: ", join ', ', @names;
		write_file("/home/grimy/Games/solutions/$pretty.solution", $solution, 1);
		push @nplets, $nplet;
	}

	for my $file (<{solution,extra_solutions}/*.solution>) {
		my @parts = solution_to_parts(slurp($file, 1));
		push @parts, omsim(@parts);
		postprocess(\@parts);
	}

	warn "merging...";

	for (0..$#halves) {
		my $a = $halves[$_];
		postprocess($_) for map { try_all_merges($a, $_) } @halves[$_..$#halves];
		mirror_parts($a);
		postprocess($_) for map { try_all_merges($a, $_) } @halves[$_..$#halves];
	}

	warn "variantifying...";

	while (1) {
		my $parts = shift((first { @$_ } @q)->@*);
		last if !$parts;
		for my $variant (variantify(@$parts)) {
			postprocess($variant);
		}
	}
}
