#!/bin/perl -s

use utf8;
use v5.36;
use warnings;
use Carp;
use Data::Dumper;
use Digest::MD5 qw(md5_base64);
use IPC::Open3;
use JSON qw(decode_json);
use List::Util qw(min max any all sum product first uniq);
use Memoize;


our ($h, $u, $n, $g, $v);

package Part {
	sub new(@args) { return bless [@args], "Part" }
	sub name :lvalue ($self)         { $$self[0] }
	sub x :lvalue ($self)            { $$self[1] }
	sub y :lvalue ($self)            { $$self[2] }
	sub size :lvalue ($self)         { $$self[3] }
	sub rotation :lvalue ($self)     { $$self[4] }
	sub instructions :lvalue ($self) { $$self[5] }
	sub track :lvalue ($self)        { $$self[6] }
	sub deleted :lvalue ($self)      { $$self[7] }

	sub loops($self) {
		return if !$self->track;
		my $track = $self->track;
		return if @$track <= 2;
		my $dx = $$track[-1][0] - $$track[0][0];
		my $dy = $$track[-1][1] - $$track[0][1];
		return abs($dx) <= 1 && abs($dy) <= 1 && abs($dx + $dy) <= 1;
	}

	sub xy($self)                    { "@$self[1, 2]" }
	sub delay($self)                 { $$self[5] =~ /\w/ ? $-[0] : 0 }
	sub pretty($self) {
		my $result = "$$self[0] @[$$self[1], $$self[2]] size=$$self[3] rotation=$$self[4]";
		$result .= ' instructions=' . $$self[5] =~ y/\0/./r if $$self[5];
		$result .= ' track=' . join ', ', map "[$$_[0], $$_[1]]", $$self[6]->@* if $$self[6];
		$result .= ' loops' if $$self[7];
		$result .= ' deleted' if $$self[8];
		return $result;
	}
}

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
	return map {
		(my ($part_name, $magic, $x, $y, $size, $rotation, $ionum, $instr_count), $sol) = unpack 'C/aCllLlLLa*', $sol;
		die "$magic != 1" if $magic != 1;
		$rotation %= 6;
		my $instructions = '';
		for (1..$instr_count) {
			(my ($offset, $instruction), $sol) = unpack 'LCa*', $sol;
			vec($instructions, $offset, 8) = $instruction;
		}

		my $result = Part::new($part_name, $x, $y, $size, $rotation, $instructions);

		if ($part_name eq 'track') {
			my @track_data = unpack 'L/(ll)a*', $sol;
			$sol = pop @track_data;

			my @track = ();
			while (@track_data) {
				my ($dx, $dy) = splice @track_data, 0, 2;
				push @track, [$x + $dx, $y + $dy];
			}
			($result->x, $result->y) = $track[0]->@*;
			$result->track = \@track;
		}

		(my ($armnum), $sol) = unpack 'La*', $sol;
		$result
	} 1..$part_count;
}

my $puzzle = 'P007';
sub parts_to_solution(@parts) {
	my $sol = pack 'LC/aC/aLL', 7, $puzzle, 'PARETO', 0, 0+@parts;
	my $arm_count = 0;
	my $input_count = 0;

	for (@parts) {
		my $ionum = $_->name eq 'input' ? $input_count++ : 0;
		my $armnum = $_->name =~ /^(arm[1236]|piston|baron)$/ ? $arm_count++ : 0;
		my $instruction_count = $_->instructions =~ y/\0//c;
		$sol .= pack 'C/aCllLlLL', $_->name, 1, $_->x, $_->y, $_->size, $_->rotation, $ionum, $instruction_count;
		$sol .= pack 'La', $-[0], $& while $_->instructions =~ /\w/g;
		if ($_->name eq 'track') {
			my @track_data = ();
			for my $point ($_->track->@*) {
				push @track_data, $point->[0] - $_->x, $point->[1] - $_->y;
			}
			$sol .= pack 'LL*', @track_data / 2, @track_data;
		}
		$sol .= pack 'L', $armnum;
	}
	return $sol;
}

sub translate_parts($parts, $dx, $dy) {
	for my $part (@$parts) {
		$part->x += $dx;
		$part->y += $dy;
		map { $_->[0] += $dx; $_->[1] += $dy } ($part->track // [])->@*;
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

my %rotational_symmetry = (
	'arm2' => 3,
	'arm3' => 2,
	'arm6' => 1,
	'bonder-speed' => 2,
	'glyph-calcification' => 1,
	'glyph-dispersion' => 3,
	'glyph-disposal' => 1,
	'input' => 1,
);

sub rotate_parts($parts, $rotation) {
	my ($xfx, $yfx, $xfy, $yfy) = $xy_rotations[$rotation]->@*;
	for my $part (@$parts) {
		my ($x, $y) = ($part->x, $part->y);
		$part->x = $x * $xfx + $y * $xfy;
		$part->y = $x * $yfx + $y * $yfy;
		if ($part->name eq 'track') {
			map {
				my ($x, $y) = @$_;
				$_->[0] = $x * $xfx + $y * $xfy;
				$_->[1] = $x * $yfx + $y * $yfy;
			} $part->track->@*;
		}
		else {
			$part->rotation += $rotation;
		}
	}
}

sub rotation_from_point($dx, $dy) {
	return first { point_eq($xy_rotations[$_], [$dx, $dy]) } 0..5;
}

sub modulize_rotation($part) {
	$part->rotation %= ($rotational_symmetry{$part->name} // 6);
	if (($part->name =~ /^(?:un)?bonder$/) && $part->rotation >= 3) {
		$part->x += $xy_rotations[$part->rotation][0];
		$part->y += $xy_rotations[$part->rotation][1];
		$part->rotation %= 3;
	}
}

sub mirror_parts($parts) {
	for my $part (@$parts) {
		$part->x += $part->y;
		$part->y *= -1;
		$part->rotation = -$part->rotation;
		$part->instructions =~ y/PRpr/prPR/;
		$_->[0] += $_->[1], $_->[1] *= -1 for ($part->track // [])->@*;
	}
}

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
		my $instrs = $part->instructions;
		next if $instrs !~ /X|C/;

		my %state = (E => 0, R => 0, A => 0);
		my $repeat_start = 0;
		my $repeat_end = -1;
		my $just_repeated = 1;
		my $trackloop = 0;

		if ($instrs =~ /A/i) {
			my $point = [ $part->x, $part->y ];
			my $track = first { $_->track and any { point_eq($_, $point) } $_->track->@* } @parts;
			$trackloop = $track->loops ? $track->track->@* : 9999;
		}

		for (my $pos = 0; $pos < length $instrs; ++$pos) {
			local $_ = chr vec($instrs, $pos, 8);
			next if $_ eq "\0";
			$state{uc $_} += ($_ eq uc ? 1 : -1);
			$state{E} = min($state{E}, 3 - $part->size) if $_ eq 'E';
			$state{E} = max($state{E}, 1 - $part->size) if $_ eq 'e';

			if ($_ eq 'C') {
				$just_repeated = 1;
				my $repeat_string = substr($instrs, $repeat_start, $repeat_end - $repeat_start + 1);
				$repeat_string ||= 'O';
				substr($instrs, $pos, length($repeat_string)) = $repeat_string;
				$pos += length($repeat_string) - 1;
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
				$reset_string ||= 'O';
				substr($instrs, $pos, length($reset_string)) = $reset_string;
				$pos += length($reset_string) - 1;
				%state = (E => 0, R => 0, A => 0);
			}

			$repeat_end = $pos;
			$just_repeated = 0;
		}

		$part->instructions = $instrs;
	}
}

sub tape_length(@parts) {
	return max map { $_->instructions =~ /\w.*/ ? length($&) : 0 } @parts;
}

sub execute_instruction($arm, $i, $track, $loops = 0) {
	$arm->size = min(3, $arm->size + 1) if $i eq 'E';
	$arm->size = max(1, $arm->size - 1) if $i eq 'e';
	$arm->rotation = ($arm->rotation - 1) % 6 if $i eq 'R';
	$arm->rotation = ($arm->rotation + 1) % 6 if $i eq 'r';
	if ($i =~ /A/i) {
		my $track_pos = first { point_eq($$track[$_], [$arm->x, $arm->y]) } 0..$#$track;
		$track_pos += $i eq 'A' ? 1 : -1;
		$track_pos = $loops ? $track_pos % @$track : max(0, min($#$track, $track_pos));
		($arm->x, $arm->y) = $track->[$track_pos]->@*;
	}
}

sub should_mirror(@parts) {
	my %sums = ();
	for (@parts) {
		my $y = $_->y;
		$y += $xy_rotations[$_->rotation][1] / 2 if $_->name =~ /^(?:un)?bonder$/;
		$sums{all} += $y;
		$sums{$_->name} += $y;
	}
	for (sort keys %sums) {
		return 1 if $sums{$_} < 0;
		return 0 if $sums{$_} > 0;
	}

	my @a = deep_copy(@parts);
	modulize_rotation($_) for @a;
	@a = sort { $b->instructions cmp $a->instructions || $a->x <=> $b->x || $a->y <=> $b->y } @a;
	my @b = deep_copy(@a);
	mirror_parts(\@b);
	my $md5_a = md5_base64(parts_to_solution(@parts));
	my $md5_b = md5_base64(parts_to_solution(@parts));
	return $md5_a gt $md5_b;
}

sub normalize($parts) {
	# Remove equilibrium
	@$parts = grep { $_->name ne 'glyph-marker' } @$parts;

	# Expand instructions
	my @arms = grep { $_->instructions } @$parts;
	expand_instructions(@$parts);
	my $tape_length = tape_length(@$parts);

	# Translate, rotate
	my ($out) = grep { $_->name eq 'out-std' } @$parts;
	translate_parts($parts, -$out->x, -$out->y);
	rotate_parts($parts, -$out->rotation);

	# Track stuff
	for my $part (@$parts) {
		next unless $part->track;
		my $track = $part->track;
		my $loops = $part->loops;
		my %points = map { ("@$_" => 1) } @$track;
		my @arms_on_track = grep { $points{$_->xy} } @arms;

		# make single arms start with a grab
		if (@arms_on_track == 1) {
			my $arm = $arms_on_track[0];
			while ($arm->instructions =~ s/^\0*+\K[^G]/\0/) {
				vec($arm->instructions, $-[0] + $tape_length, 8) = ord $&;
				execute_instruction($arm, $&, $track, $loops);
			}
		}

		# unmerge unnecessarily merged tracks
		elsif (all { $_->instructions =~ /A.*a|a.*A/ } @arms_on_track) {
			my @used_segment = ();
			for my $arm (@arms_on_track) {
				my $track_pos = first { point_eq($$track[$_], [$arm->x, $arm->y]) } 0..$#$track;
				while ($arm->instructions =~ /A/gi) {
					$used_segment[++$track_pos] = 1 if $& eq 'A';
					$used_segment[$track_pos--] = 1 if $& eq 'a';
					$track_pos = $loops ? $track_pos % @$track : max(0, min($#$track, $track_pos));
				}
			}
			$used_segment[0] = delete($used_segment[@$track]) && $loops;
			my ($a, $b) = grep { !$used_segment[$_] } 0..$#$track;
			if ($b) {
				my @new_track = @$track[$b..$#$track, 0..$a-1];
				push @$parts, Part::new('track', 0, 0, 1, 0, '', [@new_track]);
				@$track = @$track[$a..$b-1];
				%points = map { ("@$_" => 1) } @$track;
				@arms_on_track = grep { $points{$_->xy} } @arms_on_track;
			}
		}

		# reverse the track if most arms on it do - before +
		if (0 < sum map { $_->instructions =~ /A/i ? (ord($&) - 81) * 2**-$-[0] : 0 } @arms_on_track) {
			$_->instructions =~ y/Aa/aA/ for @arms_on_track;
			@$track = reverse @$track;
		}

		# normalize trackloop start point
		if ($loops) {
			my @sorted_points = sort {
				abs($$a[1]) <=> abs($$b[1]) ||
				($$a[0] * 2 + $$a[1]) <=> ($$b[0] * 2 + $$b[1])
			} @$track;
			my $first = first { point_eq($$track[$_], $sorted_points[0]) } 0..$#$track;
			@$track = @$track[$first..$#$track, 0..$first-1];
		}

		@$part[1, 2] = $track->[0]->@*;
	}

	# Remove noops and start delay
	map { $_->instructions =~ s/O/\0/g; $_->instructions =~ s/\0+$// } @arms;
	my $start_delay = min map { $_->delay } @arms;
	$_->instructions = substr($_->instructions, $start_delay) for @arms;

	# Divide period
	for (5, 4, 3, 2) {
		next if $tape_length % $_;
		my $period = $tape_length / $_;
		next if any {
			my %h = map { s/\0+$//r => 1 } $_->instructions =~ /(?:^\0+)?\K.{1,$period}/g;
			keys %h > 1
		} @arms;
		$_->instructions =~ s/^\0*+.{$period}\K.*// for @arms;
		$tape_length = $period;
	}

	# Mirror if needed
	mirror_parts($parts) if should_mirror(@$parts);

	# Modulize rotation
	modulize_rotation($_) for @$parts;

	# Sort
	@$parts = sort { $b->instructions cmp $a->instructions || $a->x <=> $b->x || $a->y <=> $b->y } @$parts;

	# Add single noop if needed
	if (tape_length(@arms) != $tape_length) {
		my $arm = first { $_->instructions =~ /^\w/ } @$parts;
		vec($arm->instructions, $tape_length - 1, 8) ||= ord 'O';
	}
}

sub deep_copy(@parts) {
	return map {
		$_ = Part::new(@$_);
		$_->track = [map [ @$_ ], $_->track->@*] if $_->track;
		$_;
	} @parts;
}

sub omsim($parts) {
	state ($out, $in, $err);
	BEGIN {
		open3($out, $in, $err, 'omsim/omsim');
		binmode $out;
	}
	print $out parts_to_solution(@$parts);
	return <$in> =~ s([/\n])()gr;
}

sub is_not_slower($parts, $limit) {
	return (omsim($parts) =~ /\d+(?=c)/) && ($& <= $limit);
}

sub minify($parts, $cycles) {
	my $old_name = $_->name;
	return if $old_name =~ /^(?:input|out-std|glyph-marker)$/;

	$_->name = 'glyph-marker';
	return 1 if is_not_slower($parts, $cycles);

	if ($old_name =~ /^arm([236])$/ and $_->instructions !~ /R/i) {
		$_->name = 'arm1';
		for my $unused (1..$1) {
			$_->rotation += 6 / $1;
			return 1 if is_not_slower($parts, $cycles);
		}
	}

	if ($old_name eq 'bonder-speed') {
		$_->name = 'bonder';
		for my $unused (1..3) {
			$_->rotation += 2;
			return 1 if is_not_slower($parts, $cycles);
		}
	}

	$_->name = $old_name;
	my $track = $_->track;

	if ($track and @$track > 2) {
		my $segment = pop @$track;
		return 1 if is_not_slower($parts, $cycles);
		push @$track, $segment;
		$segment = shift @$track;
		return 1 if is_not_slower($parts, $cycles);
		unshift @$track, $segment;
	}

	return 0;
}

sub minimize_loop_length($parts) {
	my @arms = grep { $_->instructions =~ /\w/ } @$parts;
	while (all { $_->instructions =~ /O$/ || $_->name eq 'glyph-marker' } @arms) {
		chop $_->instructions for @arms;
		if (!omsim($parts)) {
			$_->instructions .= 'O' for @arms;
			return;
		}
	}
}

sub halvify(@parts) {
	my @inputs = grep { $_->name eq 'input' } @parts;
	die if @inputs == 0;
	return [ @parts ] if @inputs == 1;

	my @halves = ();
	for my $input (@inputs) {
		my $copy = [ deep_copy(grep { $_ != $input } @parts) ];
		my $score = omsim($copy);
		if ($score =~ /\d+(?=c)/) {
			my $cycles = $&;
			expand_instructions(@$copy);
			my $tape_length = tape_length(@$copy);
			for (@$copy) {
				next unless $_->instructions =~ /\w/;
				$_->instructions .= 'O' x ($-[0] + $tape_length - length($_->instructions));
			}
			1 while any { minify($copy, $cycles) } @$copy;
			minimize_loop_length($copy);
			push @halves, $copy;
		}
	}
	return @halves;
}

sub add_repeats($parts, $period) {
	for (@$parts) {
		next unless $_->instructions =~ /\w/;
		vec($_->instructions, $-[0] + $period, 8) = ord 'C';
	}
}

my %part_points = (
	'glyph-life-and-death' => [[1, 0], [0, 1], [1, -1]],
	'bonder' => [[1, 0]],
	'bonder-prisma' => [[1, 0], [0, 1]],
	'bonder-speed' => [[1, 0], [-1, 1], [0, -1]],
	'unbonder' => [[1, 0]],
	'glyph-dispersion' => [[1, 0], [1, -1], [0, -1], [-1, 0]],
	'glyph-disposal' => [[1, 0], [0, 1], [-1, 1], [-1, 0], [0, -1], [1, -1]],
	'glyph-duplication' => [[1, 0]],
	'glyph-projection' => [[1, 0]],
	'glyph-purification' => [[1, 0], [0, 1]],
	'glyph-unification' => [[0, 1], [-1, 1], [0, -1], [1, -1]],

	'out-std' => [[1, 0]],
);

sub part_points($part) {
	return $part->track->@* if $part->name eq 'track';
	my $base = [$part->x, $part->y];
	my $extras = $part_points{$part->name};
	return $base if !$extras;
	my ($xfx, $yfx, $xfy, $yfy) = $xy_rotations[$part->rotation % 6]->@*;
	return $base, map [
		$part->x + $xfx * $_->[0] + $xfy * $_->[1],
		$part->y + $yfx * $_->[0] + $yfy * $_->[1],
	], @$extras;
}

sub point_eq($a, $b) {
	return $a->[0] == $b->[0] && $a->[1] == $b->[1];
}

sub merge_tracks($a, $b, $map) {
	my @a = $a->track->@*;
	my @b = $b->track->@*;
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

	map { $_ = $a if $_ == $b } $$map{"@$_"}->@* for @pre, @post;
	$a->track = [@pre, @a, @post];
	$b->deleted = 1;
}

sub compute_trackmap($parts) {
	my %point_to_track = ();
	my %arm_to_track = ();
	for my $part (reverse @$parts) {
		$point_to_track{"@$_"} = $part for ($part->track // [])->@*;
		$arm_to_track{$part} = $point_to_track{$part->xy} if $part->instructions;
	}
	return %arm_to_track;
}

sub track_eq($a, $b) {
	return all { point_eq($$a[$_], $$b[$_]) } 0..min($#$a, $#$b);
}

sub handle_tribonder_overlap($bonder, $tribonder) {
	my %tribonder_point = map { ("@$_" => 1) } part_points($tribonder);
	return unless all { $tribonder_point{"@$_"} } part_points($bonder);
	return $bonder->deleted = 1;
}

sub handle_overlap($a, $b, $parts, $map) {
	return 1 if $a->deleted || $b->deleted || $a == $b;
	my ($a_is_track, $a_is_arm) = ($a->name eq 'track', $a->name =~ /^(?:arm[1236]|piston)$/);
	my ($b_is_track, $b_is_arm) = ($b->name eq 'track', $b->name =~ /^(?:arm[1236]|piston)$/);

	if ($a_is_track && $b_is_track) {
		return 1 if merge_tracks($a, $b, $map);
		my %arm_to_track = compute_trackmap($parts);
		my @arms_on_a = grep { ($arm_to_track{$_} // 0) == $a } @$parts;
		$_->instructions =~ y/Aa/aA/ for @arms_on_a;
		$a->track = [reverse $a->track->@*];
		return merge_tracks($a, $b, $map);
	}

	if ($a_is_arm && $b_is_arm) {
		if ($a->instructions =~ /A/ && $b->instructions =~ /A/) {
			my %arm_to_track = compute_trackmap($parts);
			if (!track_eq($arm_to_track{$a}->track, $arm_to_track{$b}->track)) {
				my $arm = index($a->instructions, 'G') > index($b->instructions, 'G') ? $a : $b;
				my $track = $arm_to_track{$arm};
				while (1) {
					return 0 unless $arm->instructions =~ s/^\0*\K\0(.*)(.)$/$2$1/;
					execute_instruction($arm, $2 =~ y/A-Za-z/a-zA-Z/r, $track->track, $track->loops);
					last if $2 =~ /A/i;
				}
				return 1;
			}
		}
		return if $a->size != $b->size;
		return 0 if $a->instructions ne $b->instructions;
		my $grippers = 1;
		my $dr = $b->rotation - $a->rotation;
		$grippers *= 2 if $a->name =~ /^arm[26]$/ or $b->name =~ /^arm[26]$/ or $dr % 2;
		$grippers *= 3 if $a->name =~ /^arm[36]$/ or $b->name =~ /^arm[36]$/ or $dr % 3;
		if ($a->name eq 'piston' or $b->name eq 'piston') {
			return if $grippers > 1;
		} else {
			$a->name = "arm$grippers";
		}
		return $b->deleted = 1;
	}

	return 1 if ($a_is_track && $b_is_arm) || ($a_is_arm && $b_is_track);
	return handle_tribonder_overlap($a, $b) if $a->name eq 'bonder' && $b->name eq 'bonder-speed';
	return handle_tribonder_overlap($b, $a) if $b->name eq 'bonder' && $a->name eq 'bonder-speed';
	return if $a->name ne $b->name;

	if ($a->name eq 'bonder') {
		my %a_point = map { ("@$_" => 1) } part_points($a);
		my @common_points = grep { $a_point{"@$_"} } part_points($b);
		return $b->deleted = 1 if @common_points == 2;
		die if @common_points != 1;
		my $point = $common_points[0];
		my $rotation_for_a = ($a->rotation & 1) ^ !point_eq($point, [$a->x, $a->y]);
		my $rotation_for_b = ($b->rotation & 1) ^ !point_eq($point, [$b->x, $b->y]);
		return if $rotation_for_a != $rotation_for_b;
		$a->name = 'bonder-speed';
		($a->x, $a->y) = @$point;
		$a->rotation = $rotation_for_a;
		return $b->deleted = 1;
	}

	return if $a->rotation != $b->rotation;
	return if $a->x != $b->x || $a->y != $b->y;
	return $b->deleted = 1;
}

sub deoverlap($parts) {
	my %map = ();
	for my $part (@$parts) {
		for my $point (part_points($part)) {
			my $overlaps = ($map{"@$point"} //= []);
			for (@$overlaps) {
				my $result = handle_overlap($part, $_, $parts, \%map);
				return $result if !$result;
			}
			push @$overlaps, $part;
		}
	}

	@$parts = grep { !$_->deleted } @$parts;

	return 1;
}

sub try_merge($half_a, $half_b) {
	my @merged = deep_copy(@$half_a, @$half_b);
	my $deoverlap_result = deoverlap(\@merged);
	return if not defined $deoverlap_result;
	my $score = omsim(\@merged) if $deoverlap_result;
	return [@merged, $score] if $score;

	my @result = ();
	my @delayed = deep_copy(@$half_a);

	for (1..3) {
		$_->instructions =~ s/(?=\w)/\0/ for @delayed;
		@merged = deep_copy(@delayed, @$half_b);
		next unless deoverlap(\@merged);
		$score = omsim(\@merged);
		if ($score) {
			push @result, [@merged, $score];
			last;
		}
	}

	@delayed = deep_copy(@$half_b);

	for (1..3) {
		$_->instructions =~ s/(?=\w)/\0/ for @delayed;
		@merged = deep_copy(@$half_a, @delayed);
		next unless deoverlap(\@merged);
		$score = omsim(\@merged);
		if ($score) {
			push @result, [@merged, $score];
			last;
		}
	}

	return @result;
}

sub try_all_merges(@halves) {
	my @periods = map { tape_length(@$_) } @halves;
	my @lengths = @periods;
	my @results = try_merge(@halves);
	return @results if uniq(@lengths) == 1;

	@halves = map [ deep_copy(@$_) ], @halves;

	for (1..6) {
		my $index = $lengths[0] < $lengths[1] ? 0 : 1;
		add_repeats($halves[$index], $lengths[$index]);
		$lengths[$index] += $periods[$index];
		push @results, try_merge(@halves);
		last if uniq(@lengths) == 1;
		last if all { $_ > 42 } @lengths;
	}

	return @results;
}

sub save_and_check(@parts) {
	my $solution = parts_to_solution(@parts);
	my $md5 = md5_base64($solution) =~ y(/)(_)r;
	return $md5 if -f "normalized/$md5.solution";
	write_file("normalized/$md5.solution", $solution, 1);

	normalize(\@parts);
	die "normalizing broke solve: $md5" if not omsim(\@parts);
	my $solution_new = parts_to_solution(@parts);
	my $md5_new = md5_base64($solution_new) =~ y(/)(_)r;
	if ($md5_new ne $md5) {
		write_file("test/$md5_new.solution", $solution_new, 1);
		die "non-idempotent normalization: $md5 => $md5_new";
	}
	return $md5;
}

sub fold_tracked_arms($parts) {
	my @arms = grep { $_->instructions =~ /\w/ } @$parts;
	for (@$parts) {
		next unless $_->name eq 'track';
		my %points = map { ("@$_" => 1) } $_->track->@*;
		my @arms_on_track = grep { $points{$_->xy} } @arms;
		next if @arms_on_track != 1;
		$arms_on_track[0]->track = $_->track;
		$_->deleted = 1;
	}
	@$parts = grep { !$_->deleted } @$parts;
}

sub unfold_tracked_arms($parts) {
	@$parts = map {
		$_->track && $_->name ne 'track' ?
			($_, Part::new('track', $_->x, $_->y, 1, 0, '', delete $$_[6])) :
			($_);
	} @$parts;
}

sub angle($ax, $ay, $bx, $by) {
	for (0..5) {
		return $_ if $ax == $bx && $ay == $by;
		($ax, $ay) = (-$ay, $ax + $ay);
	}
}

sub grab_point($x, $y, $size, $rotation) {
	my ($xfx, $yfx) = $xy_rotations[$rotation]->@*;
	return $x + $size * $xfx, $y + $size * $yfx;
}

sub part_variants($part, $would_shorten_tape) {
	my ($instructions, $track) = ($part->instructions, $part->track);

	# Not an arm? Don’t do anything
	return if $instructions !~ /\w/;

	# Already sharing a track? Don’t do anything
	return if $instructions =~ /A/i && !$track;

	# Multi-arms can be converted to single arms, but nothing else
	if ($part->name =~ /^arm([236])$/) {
		return map {
			Part::new('arm1', $part->x, $part->y, $part->size,
				$part->rotation + $_ * (6 / $1), $instructions =~ y/gO/X\0/r);
		} 1..$1;
	}

	my ($grab_x, $grab_y) = grab_point($part->x, $part->y, $part->size, $part->rotation);
	my @points = ([$grab_x, $grab_y]);
	my $index = 0;
	my $require_loops = 0;
	my $grab_index = 0;
	my $loops = $part->loops;

	$instructions =~ s{[ERA]}{
		execute_instruction($part, $&, $track, $loops);
		my $point = [grab_point($part->x, $part->y, $part->size, $part->rotation)];
		my $last_index = $index;
		$index = first { point_eq($points[$_], $point) } 0..$#points;
		if (!defined($index)) {
			if ($last_index == $#points) {
				push @points, $point;
				$index = $#points;
				'>'
			} elsif ($last_index == 0) {
				unshift @points, $point;
				$index = 0;
				'<'
			} else {
				return;
			}
		} elsif ($index == $last_index + 1) {
			'>'
		} elsif ($index == $last_index - 1) {
			'<'
		} elsif ($index == $last_index) {
			'O'
		} elsif ($index == 0 && $last_index == $#points) {
			$require_loops = 1;
			'>'
		} elsif ($index == $#points && $last_index == 0) {
			$require_loops = 1;
			'<'
		} else {
			return;
		}
	}gie;

	my @result = ();

	my $add_arm = sub ($name, $size, $rotation, @args) {
		$rotation %= 6;
		my ($x, $y) = grab_point($grab_x, $grab_y, -$size, $rotation);
		push @result, Part::new($name, $x, $y, $size, $rotation, @args);
	};

	# Pivots only)
	if (@points == 1) {
		die if $instructions =~ /[><]/;
		for my $rotation (0..5) {
			for my $size (1..3) {
				$add_arm->('arm1', $size, $rotation, $instructions);
			}
		}
		return @result;
	}

	my @dx = map { $points[$_][0] - $points[$_ - 1][0] } 1..$#points;
	my @dy = map { $points[$_][1] - $points[$_ - 1][1] } 1..$#points;
	my @angles = map { angle($dx[$_ - 1], $dy[$_ - 1], $dx[$_], $dy[$_]) } 1 .. $#dx;
	my $angles = join '', map { $_ // '?' } @angles;
	my $size = max(map abs, @dx, @dy);

	# Fixed arm
	if ($angles =~ /^1*$|^5*$/) {
		my $grippers = (@dx % 2 ? 2 : 1) * (@dx % 3 ? 3 : 1);
		my @multi_instrs = ($instructions =~ s(g\K[^gG]*)($&=~y/></\0\0/r)erg);
		push @multi_instrs, $multi_instrs[0] =~ s/\0$/O/r if $would_shorten_tape;
		my $rotation = rotation_from_point(0 <=> $dx[0], 0 <=> $dy[0]);
		if ($angles =~ /^1*$/) {
			# Couter-clockwise
			$add_arm->('arm1', $size, $rotation + 1, $instructions =~ y/></rR/r);
			$add_arm->("arm$grippers", $size, $rotation + 1, $instructions =~ y/></rR/r) for @multi_instrs;
		}
		if ($angles =~ /^5*$/) {
			# Clockwise
			$add_arm->('arm1', $size, $rotation - 1, $instructions =~ y/></Rr/r);
			$add_arm->("arm$grippers", $size, $rotation - 1, y/></Rr/r) for @multi_instrs;
		}
	}

	# TODO handle some unusual bends

	return @result if $size > 1;

	# Tracked arm
	for my $rotation (0..5) {
		my ($xfx, $yfx) = $xy_rotations[$rotation]->@*;
		for my $size (1..3) {
			$add_arm->('arm1', $size, $rotation, $instructions =~ y/></Aa/r,
			[map { [$$_[0] - $size * $xfx, $$_[1] - $size * $yfx] } @points]);
		}
	}

	# TODO tracked arms with rotates/pistons

	# Piston
	my $rotation = rotation_from_point($dx[0], $dy[0]);

	if ($angles =~ /^0?$/) {
		for my $size (1 .. 4 - @points) {
			$add_arm->('piston', $size, $rotation, $instructions =~ y/></Ee/r);
		}
		for my $size (@points .. 3) {
			$add_arm->('piston', $size, $rotation + 3, $instructions =~ y/></eE/r);
		}
	}

	# Bent pistons
	my $bent_instrs = sub ($lo, $hi, $limit) {
		my $state = 0;
		if ($limit < 0 or (@dx - $limit) < 0) {
			say $limit, " ", 0+@dx;
		}
		my @plus = (($lo) x $limit, ($hi) x (@dx - $limit));
		my @minus = map { y/A-Za-z/a-zA-Z/r } @plus;
		my $result = $instructions =~ s{[><]}{
			$& eq '>' ? $plus[$state++] : $minus[--$state];
		}gre;
		return $result;
	};
	my $n = 0 + @angles;

	$add_arm->('piston', 2, $rotation + 3, $bent_instrs->('e', 'R', 1))         if $angles =~ /^15*$/;
	$add_arm->('piston', 2, $rotation + 3, $bent_instrs->('e', 'r', 1))         if $angles =~ /^51*$/;
	$add_arm->('piston', 1, $rotation - 2, $bent_instrs->('r', 'E', @angles+0)) if $angles =~ /^1*5$/;
	$add_arm->('piston', 1, $rotation + 2, $bent_instrs->('R', 'E', @angles+0)) if $angles =~ /^5*1$/;
	$add_arm->('piston', 3, $rotation + 3, $bent_instrs->('e', 'R', 2))         if $angles =~ /^015*$/;
	$add_arm->('piston', 3, $rotation + 3, $bent_instrs->('e', 'r', 2))         if $angles =~ /^051*$/;
	$add_arm->('piston', 1, $rotation - 2, $bent_instrs->('r', 'E', @angles-1)) if $angles =~ /^1*50$/;
	$add_arm->('piston', 1, $rotation + 2, $bent_instrs->('R', 'E', @angles-1)) if $angles =~ /^5*10$/;

	return @result;
}

sub variantify(@parts) {
	@parts = deep_copy(@parts);
	normalize(\@parts);
	fold_tracked_arms(\@parts);

	my @tape_lengths = map { $_->instructions =~ /\w.*/ ? length($&) : 0 } @parts;
	my $tape_length = max @tape_lengths;
	my @longest_tape_indices = grep { $tape_lengths[$_] == $tape_length } 0..$#tape_lengths;
	my $unique_longest_tape_index = @longest_tape_indices == 1 ? $longest_tape_indices[0] : -1;

	my @variants = ();

	for my $i (0..$#parts) {
		for my $part_variant (part_variants($parts[$i], $i == $unique_longest_tape_index)) {
			my @variant = deep_copy(@parts);
			$variant[$i] = $part_variant;
			unfold_tracked_arms(\@variant);
			next unless deoverlap(\@variant);
			my $score = omsim(\@variant);
			push @variants, [@variant, $score] if $score;
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
say "old: $_" for grep { !$good{$_} } <solution/*.solution>;

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
		my $goal = omsim(\@parts);
		my @inputs = grep { $_->name eq 'input' } @parts;
		my @halves = halvify(@parts);

		normalize($_) for @halves;
		++$new_md5{$_} for map { save_and_check(@$_) } @halves;

		if (@inputs == 1) {
			die if @halves != 1;
			my $attempt = omsim($halves[0]);
			write_file("test/half.solution", parts_to_solution(@{$halves[0]}), 1);
			die "$attempt ne $goal" if $attempt ne $goal;
		}
		elsif (@halves == 2) {
			my @attempts = try_all_merges(@halves);
			mirror_parts($halves[0]);
			push @attempts, try_all_merges(@halves);
			next if any { $_->[-1] eq $goal } @attempts;
			my @tape_lengths = map { tape_length(@$_) } @halves;
			if ($tape_lengths[0] > $tape_lengths[1]) {
				@tape_lengths = reverse @tape_lengths;
				@halves = reverse @halves;
			}
			if ("@tape_lengths" =~ /^4 12$|^13 13$/) {
				my $arm = first { $_->instructions =~ /\w/ } $halves[1]->@*;
				vec($arm->instructions, $arm->delay + $tape_lengths[1], 8) = ord 'O';
				push @attempts, try_all_merges(@halves);
			}
			next if any { $_->[-1] eq $goal } @attempts;
			die join "\n", $goal, map { $_->[-1] } @attempts;
		}
	}

	warn "new md5: $_" for grep { !$old_md5{$_} } keys %new_md5;
	warn "old md5: $_" for grep { !$new_md5{$_} } keys %old_md5;
}

if ($v) {
	my %known = ();
	my @q = ([]);
	my @halves = map [solution_to_parts(slurp($_, 1))], <normalized/*.solution>;

	my ($cache_hit, $cache_miss) = (0, 0);

	sub postprocess($parts) {
		my $score = pop @$parts;
		normalize($parts);
		my $solution = parts_to_solution(@$parts);
		my $md5 = md5_base64(parts_to_solution(@$parts)) =~ y(/)(_)r;
		++$cache_hit, return if $known{$md5}++;
		++$cache_miss;
		say "$cache_hit hits, $cache_miss misses" if !($cache_miss & ($cache_miss - 1));
		my $nplet = [$score =~ /[\d.]+/g];
		my $outV = count_outparetos($nplet, $MASK_V, \@nplets);
		my $outINF = count_outparetos($nplet, $MASK_INF, \@nplets);
		my $true_outs = min($outV, $outINF);
		push $q[$true_outs]->@*, $parts if $true_outs < 4;
		return if $true_outs;
		my @names = name($nplet, \@nplets);
		say "$score: ", join ', ', @names;
		write_file("/home/grimy/Games/solutions/$score.solution", $solution, 1);
		push @nplets, $nplet;
	}

	for my $file (<{solution,extra_solutions}/*.solution>) {
		my @parts = solution_to_parts(slurp($file, 1));
		my $score = omsim(\@parts);
		push @parts, $score;
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
	my $count = 0;
	while (my $entry = first { @$_ } @q) {
		my $parts = shift @$entry;
		++$count;
		say "$count: ", join ', ', map { 0+@$_ } @q if !($count & ($count - 1));
		postprocess($_) for variantify(@$parts);
	}
}

for my $file (<solution/*.solution>) {
	my @parts = solution_to_parts(slurp($file, 1));
	my $score = omsim(\@parts);
	die if $score !~ /\d+(?=c)/;
	my $cycles = $&;
	expand_instructions(@parts);
	next unless any { length($_->instructions) > $cycles } @parts;
	$_->instructions =~ s/g\K[^g]+$// for @parts;
	my $tape_length = tape_length(@parts);
	my $arm = first { $_->instructions =~ /^\w/ } @parts;
	for ($tape_length .. $cycles + 1) {
		vec($arm->instructions, $_ - 1, 8) ||= ord 'O';
		$score = omsim(\@parts);
		next unless $score;
		my $nplet = [$score =~ /[\d.]+/g];
		my $outV = count_outparetos($nplet, $MASK_V, \@nplets);
		next if $outV;
		my $solution = parts_to_solution(@parts);
		say $score;
		write_file("/home/grimy/Games/solutions/$score.solution", $solution, 1);
	}
}

if (1) {
	$puzzle = 'c400776884268947';
	$part_points{'out-std'} = undef;

	sub count_arms(@variants) {
		my %count = (track => 0, piston => 0, fixed => 0, multi => 0);
		for my $variant (@variants) {
			my %names = map { $_->name => 1 } @$variant[0..$#$variant - 1];
			++$count{$names{track} ? 'track' : $names{piston} ? 'piston' : $names{arm1} ? 'fixed' : 'multi'};
		}
		return "track=$count{track} piston=$count{piston} fixed=$count{fixed} multi=$count{multi}";
	}

	sub test_variants($name, $solve) {
		my $score = omsim($solve);
		my @variants = variantify(@$solve);
		my $arm_counts = count_arms(@variants);
		printf "%-16s %-36s %s\n", $name, $score, $arm_counts;
		for my $variant (@variants) {
			pop @$variant;
			my $variant_arm_counts = count_arms(variantify(@$variant));
			my $has_multiarm = any { $_->name =~ /^arm[236]$/ } @$variant;
			my $expected = $has_multiarm ? 'track=0 piston=0 fixed=1 multi=0' : $arm_counts;
			die "$variant_arm_counts ne $expected" if $variant_arm_counts ne $expected;
		}
	}

	for my $size (1..3) {
		test_variants("size $size simple", [
			Part::new('out-std', 0, 0, 1, 0, ''),
			Part::new('input', $size, 0, 1, 0, ''),
			Part::new('arm1', 0, $size, $size, 5, 'GRgr'),
		]);

		test_variants("size $size double", [
			Part::new('out-std', 0, 0, 1, 0, ''),
			Part::new('input', $size, $size, 1, 0, ''),
			Part::new('arm1', 0, $size, $size, 0, 'GRRgrr'),
		]);

		test_variants("size $size triple", [
			Part::new('out-std', 0, 0, 1, 0, ''),
			Part::new('input', 0, 2*$size, 1, 0, ''),
			Part::new('arm1', 0, $size, $size, 1, 'GRRRgrrr'),
		]);

		test_variants("size $size quad", [
			Part::new('out-std', 0, 0, 1, 0, ''),
			Part::new('input', -$size, 2*$size, 1, 0, ''),
			Part::new('arm1', 0, $size, $size, 2, 'GRRRRgRR'),
		]);

		test_variants("size $size quint", [
			Part::new('out-std', 0, 0, 1, 0, ''),
			Part::new('input', -$size, $size, 1, 0, ''),
			Part::new('arm1', 0, $size, $size, 3, 'GRRRRRgR'),
		]);
	}

	test_variants("pivot only", [
		Part::new('out-std', 0, 0, 1, 0, ''),
		Part::new('input', 0, 0, 1, 0, ''),
		Part::new('arm1', 1, 0, 1, 3, 'GPg'),
	]);

	test_variants("3 straight", [
		Part::new('out-std', 0, 0, 1, 0, ''),
		Part::new('input', 2, 0, 1, 0, ''),
		Part::new('piston', 3, 0, 1, 3, 'GEEgee'),
	]);

	test_variants("triangle", [
		Part::new('out-std', 0, 0, 1, 0, ''),
		Part::new('input', 1, 0, 1, 0, ''),
		Part::new('track', -1, 0, 1, 0, '', [[-1, 0], [-2, 1], [-2, 0]], 1),
		Part::new('arm1', -1, 0, 2, 0, 'GAAgA'),
	]);

	test_variants("bent 1", [
		Part::new('out-std', 0, 0, 1, 0, ''),
		Part::new('input', 2, 1, 1, 0, ''),
		Part::new('track', 1, 2, 1, 0, '', [[1, 2], [1, 1], [0, 1], [-1, 1]]),
		Part::new('arm1', 1, 2, 1, 5, 'GAAAgaaa'),
	]);

	test_variants("bent 2", [
		Part::new('out-std', 0, 0, 1, 0, ''),
		Part::new('input', 2, 1, 1, 0, ''),
		Part::new('track', 1, 2, 1, 0, '', [[1, 2], [0, 2], [0, 1], [-1, 1]]),
		Part::new('arm1', 1, 2, 1, 5, 'GAAAgaaa'),
	]);

	test_variants("bent 3", [
		Part::new('out-std', 0, 0, 1, 0, ''),
		Part::new('input', 2, 1, 1, 0, ''),
		Part::new('track', 1, 2, 1, 0, '', [[1, 2], [0, 2], [-1, 2], [-1, 1]]),
		Part::new('arm1', 1, 2, 1, 5, 'GAAAgaaa'),
	]);

	test_variants("bent 4", [
		Part::new('out-std', 0, 0, 1, 0, ''),
		Part::new('input', 3, 1, 1, 0, ''),
		Part::new('track', 2, 2, 1, 0, '', [[2, 2], [1, 2], [1, 1], [0, 1], [-1, 1]]),
		Part::new('arm1', 2, 2, 1, 5, 'GAAAAgaaaa'),
	]);

	test_variants("bent 5", [
		Part::new('out-std', 0, 0, 1, 0, ''),
		Part::new('input', 3, 1, 1, 0, ''),
		Part::new('track', 2, 2, 1, 0, '', [[2, 2], [1, 2], [0, 2], [0, 1], [-1, 1]]),
		Part::new('arm1', 2, 2, 1, 5, 'GAAAAgaaaa'),
	]);
}

if (0) {
	my %score_map = ();
	my %layout_map = ();
	my %bsm = ();

	for my $file (<normalized/*.solution>) {
		my @parts = solution_to_parts(slurp($file, 1));
		my $score = omsim(\@parts);
		$bsm{$file} = $score;
		push $score_map{$score}->@*, $file;
		$_->instructions = '' for @parts;
		my $solution = parts_to_solution(@parts);
		my $md5 = md5_base64($solution) =~ y(/)(_)r;
		push $layout_map{$md5}->@*, $file;
	}

	for (keys %score_map) {
		say "duped score: $_ @{$score_map{$_}}" if @{$score_map{$_}} > 1;
	}

	for (keys %layout_map) {
		if (@{$layout_map{$_}} > 1) {
			say "* duped layout:";
			say "** $_ = $bsm{$_}" for @{$layout_map{$_}};
		}
	}
}

if (0) {
	for my $file (<normalized/*.solution>) {
		my @parts = solution_to_parts(slurp($file, 1));
		say omsim(\@parts);
	}
}
