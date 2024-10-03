#!/bin/perl

use utf8;
use v5.36;
use warnings;
use Carp;
use IO::Select;
use IPC::Open3;
use List::Util qw(min max any all sum sum0 product first uniq);
use JSON qw(decode_json);
use Time::HiRes qw(time);


my $LEVEL_CODE = 'P007';
my $SOLUTION_NAME = 'PARETO';
my $CYCLE_LIMIT = 0;

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
	sub conduit_id :lvalue ($self)   { $$self[8] }

	sub copy($self) {
		my $result = Part::new(@$self);
		$result->track &&= [$result->track->@*];
		return $result;
	}

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

sub expand_nplet($nplet) {
	push @$nplet, sum(@$nplet[1..3]), sum(@$nplet[1..4]), product(@$nplet[1..3]);
}

sub nplet_to_filename {
	my $result = "$_[2]g$_[1]c$_[3]a$_[4]i$_[5]h";
	$result .= ($_[6] / 2) . 'w';
	$result .= $_[7] . 'b';
	$result .= ($_[9] / 100) . 'r' if $_[8] < 999999999;
	$result .= 'T' if !$_[0];
	$result .= 'O' if $_[14];
	return $result;
}

sub nplet_eq($a, $b, @metrics) {
	return all { $$a[$_] == $$b[$_] } @metrics ? @metrics : 0..$#$a;
}

sub nplet_le($a, $b, @metrics) {
	return all { $$a[$_] <= $$b[$_] } @metrics ? @metrics : 0..$#$a;
}

sub nplet_lt($a, $b, @metrics) {
	return nplet_le($a, $b, @metrics) && !nplet_eq($a, $b, @metrics);
}

sub solution_to_parts($sol) {
	(my ($magic, $level, $sol_name, $part_count), $sol) = unpack 'LC/aC/aL/(x8)La*', $sol;
	die "$magic != 7" if $magic != 7 && $magic != 5;
	$LEVEL_CODE = $level;
	return map {
		(my ($part_name, $magic, $x, $y, $size, $rotation, $ionum, $instr_count), $sol) = unpack 'C/aCllLlLLa*', $sol;
		my $pretty_name = $part_name =~ s/[^ -~]/./gr;
		die "<$pretty_name>, $magic, $x, $y, $size, $rotation, $ionum, $instr_count" if $magic != 1;
		$rotation %= 6;
		my $instructions = '';
		for (1..$instr_count) {
			(my ($offset, $instruction), $sol) = unpack 'LCa*', $sol;
			return if not defined $sol;
			vec($instructions, $offset, 8) = $instruction;
		}

		my $result = Part::new($part_name, $x, $y, $size + $ionum, $rotation, $instructions);

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

		if ($part_name eq 'pipe') {
			($result->conduit_id, my @track_data) = unpack 'LL/(ll)a*', $sol;
			$sol = pop @track_data;
			my @track = ();
			push @track, [splice @track_data, 0, 2] while @track_data;
			$result->track = \@track;
		}
		$result
	} 1..$part_count;
}

sub parts_to_solution(@parts) {
	my $sol = pack 'LC/aC/aLL', 7, $LEVEL_CODE, $SOLUTION_NAME, 0, 0+@parts;
	my $arm_count = 0;

	for (@parts) {
		my ($size, $ionum) = ($_->size, 0);
		($size, $ionum) = (1, $size - 1) if $_->name =~ /^(?:input|out-std|out-rep)$/;
		my $armnum = $_->name =~ /^(?:arm[1236]|piston|baron)$/ ? $arm_count++ : 0;
		my $instruction_count = $_->instructions =~ y/\0//c;
		$sol .= pack 'C/aCllLlLL', $_->name, 1, $_->x, $_->y, $size, $_->rotation, $ionum, $instruction_count;
		$sol .= pack 'La', $-[0], $& while $_->instructions =~ /\w/g;
		if ($_->name eq 'track') {
			my @track_data = ();
			for my $point ($_->track->@*) {
				push @track_data, $point->[0] - $_->x, $point->[1] - $_->y;
			}
			$sol .= pack 'LL*', @track_data / 2, @track_data;
		}
		$sol .= pack 'L', $armnum;
		if ($_->name eq 'pipe') {
			my @track_data = map { @$_ } $_->track->@*;
			$sol .= pack 'LLL*', $_->conduit_id, @track_data / 2, @track_data;
		}
	}
	write_file("test.solution", $sol, 1);
	return $sol;
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
		my ($x, $y) = ($part->x, $part->y);
		$part->x = $x * $xfx + $y * $xfy;
		$part->y = $x * $yfx + $y * $yfy;
		$part->track &&= [map [
			$$_[0] * $xfx + $$_[1] * $xfy,
			$$_[0] * $yfx + $$_[1] * $yfy,
		], $part->track->@*];
		$part->rotation += $rotation unless $part->track;
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

sub deep_copy(@parts) {
	return map { $_->copy } @parts;
}

sub omsim($parts) {
	state ($out, $in, $err, $selector);
	BEGIN {
		open3($out, $in, $err, 'omsim/omsim');
		binmode $out;
		$selector = IO::Select->new();
		$selector->add($in);
	}

	<$in> while $selector->can_read(0);
	print $out pack('L', $CYCLE_LIMIT), parts_to_solution(@$parts);
	return [map { 0+$_ } <$in> =~ /\d+/g];
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
	return 1 if ($a->name . ' ' . $b->name) =~ /^input out-std$|^out-std input$/;
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

sub grab_point($x, $y, $size, $rotation) {
	my ($xfx, $yfx) = $xy_rotations[$rotation]->@*;
	return $x + $size * $xfx, $y + $size * $yfx;
}

sub part_variants($part, $would_shorten_tape) {
	if ($part->name =~ 'piston') {
		$part = Part::new(@$part);
		$part->name = 'arm1';
		return $part;
	}
	if ($part->name eq 'track' && $part->track->@* > 1) {
		my ($a, $b) = ($part->copy, $part->copy);
		pop $a->track->@*;
		shift $b->track->@*;
		return ($a, $b);
	}
	if ($part->name =~ /^arm([236])$/) {
		return map {
			Part::new('arm1', $part->x, $part->y, $part->size, $part->rotation + $_ * (6 / $1),
				$part->instructions =~ s/g[^G]*/'X' . "\0" x (length($&) - 1)/gre, $part->track);
		} 1..$1;
	}
	if ($part->name eq 'bonder-speed') {
		return map {
			Part::new('bonder', $part->x, $part->y, $part->size, $part->rotation + $_ * 2, '');
		} 1..3;
	}
	return;
}

sub variantify(@parts) {
	@parts = deep_copy(@parts);
	my $time = time();
	my $original_nplet = omsim(\@parts);
	$time = (time() - $time) * @parts;
	warn("skipping: $time"), return if $time > 30;

	my @tape_lengths = map { $_->instructions =~ /\w.*/ ? length($&) : 0 } @parts;
	my $tape_length = max @tape_lengths;
	my @longest_tape_indices = grep { $tape_lengths[$_] == $tape_length } 0..$#tape_lengths;
	my $unique_longest_tape_index = @longest_tape_indices == 1 ? $longest_tape_indices[0] : -1;

	my @variants = ();

	for my $i (0..$#parts) {
		for my $part_variant (part_variants($parts[$i], $i == $unique_longest_tape_index)) {
			my @variant = deep_copy(@parts);
			$variant[$i] = $part_variant;
			my $nplet = omsim(\@variant);
			push @variants, [@variant, $nplet] if @$nplet;
		}
	}

	for my $i (0..$#parts) {
		next if $parts[$i]->name =~ /^(?:input|out-std|out-rep|pipe)$/;
		my @variant = deep_copy(@parts[0..$i-1, $i+1..$#parts]);
		my $nplet = omsim(\@variant);
		push @variants, [@variant, $nplet] if @$nplet && !nplet_eq($nplet, $original_nplet);
	}

	return @variants;
}

########
# Main #
########

my @puzzles = map [split ' '], split "\n", slurp('puzzles.txt');

sub letters_to_list {
	return [map { "TCGAIHWBLRahwbOSZX" =~ $_; @- } /./g];
}

my %puzzle_type = (
	NORMAL => {
		category_names => [qw(
			GC GA GI GX CG CA CI CX AG AC AX AI IG IC IA S Z
			OGC OCX OAC OIC TIG TIC TIA TG TC
			HG HC WG WC BG BC
			RG RA RI ORG HR WR BR
		)],
		manifolds => [map { letters_to_list } qw(GCAITLO GCHITLO GCWITLO GCBITLO GRaITO GRhITO GRwITO GRbITO)],
	},
	POLYMER => {
		category_names => [qw(
			GC GA GI GX CG CA CI CX AG AC AX AI IG IC IA S Z
			OGC OCX OAC OIC TIG TIC TIA TG TC
			HG HC
			RG RA RI ORG HR
		)],
		manifolds => [map { letters_to_list } qw(GCAITLO GCHITLO GRaITO GRhITO)],
	},
	PRODUCTION => {
		category_names => [qw(GC GI GX CG CI CX IG IC IX S RG RI)],
		manifolds => [map { letters_to_list } qw(GCAITLO GRaITO)],
	},
);

for my $key (keys %puzzle_type) {
	my $type = $puzzle_type{$key};
	$$type{categories} = [map {
		local $_ = $_;
		s/^O// || s/^/O/;
		if ($key eq 'PRODUCTION') {
			$_ .= /R/ ? 'GIaT' : 'GCILAT';
		} else {
			$_ .= 'G' . 'C'x!/R/ . 'A'x!/[AHWB]/ . 'L'x!/R/ . 'IT';
			y/AHWB/ahwb/ if /R/;
		}
		letters_to_list
	} $$type{category_names}->@*];
}

sub is_record($this, $context, @metrics) {
	return 1 if !@$context;
	return if !@metrics;
	my $metric = shift @metrics;
	my @ties = ();
	for my $that (@$context) {
		die "[@$this] [@$that]" if not defined $$this[$metric];
		return if $$that[$metric] < $$this[$metric];
		push @ties, $that if $$that[$metric] == $$this[$metric];
	}
	return is_record($this, \@ties, @metrics);
}

sub is_pareto($a, $context, $manifold) {
	return not any { nplet_le($_, $a, @$manifold) } @$context;
}

sub is_pareto_anywhere($a, $context, $puzzle_type) {
	return any { is_pareto($a, $context, $_) } $$puzzle_type{manifolds}->@*;
}

sub outparetos($a, $b, $puzzle_type) {
	return any { nplet_lt($a, $b, @$_) } $$puzzle_type{manifolds}->@*;
}

sub get_records($nplet, $context, $puzzle_type) {
	my @category_names = $$puzzle_type{category_names}->@*;
	my @categories = $$puzzle_type{categories}->@*;
	return @category_names[grep { is_record($nplet, $context, $categories[$_]->@*) } 0..$#categories];
}

sub json_to_nplet($json) {
	my $inf = 4294967295;
	my $score = decode_json($json =~ s/"INF"|Infinity/0/rg)->{score};
	my $a = $$score{areaINF};
	return [
		$$score{trackless} ? 0 : 1,
		$$score{cycles},
		$$score{cost},
		$$score{area},
		$$score{instructions},
		$$score{height} || $inf,
		($$score{width} || 0) * 2 || $inf,
		$$score{boundingHex} || $inf,
		$$score{rate} ? 0 : 1,
		$$score{rate} ? $$score{rate} * 100 : $inf,
		$a ? int($$a{value} * 1000 ** $$a{level}) : $inf,
		$$score{heightINF} || $inf,
		($$score{widthINF} || 0) * 2 || $inf,
		$$score{boundingHexINF} || $inf,
		$$score{overlap} ? 1 : 0,
	];
}

my $git_output = `git --git-dir=om-leaderboard/.git --work-tree=om-leaderboard pull`;

my $max_age = (any { $_ eq '--all' } @ARGV) ? 99999 : -M 'changes.json';
END { `touch changes.json` }

for my $puzzle (@puzzles) {
	my $puzzle_path = "$$puzzle[1]/$$puzzle[0]";
	my $puzzle_type = $puzzle_type{$$puzzle[2]} or die;
	next unless -M "om-leaderboard/$puzzle_path" < $max_age;
	say $puzzle_path;

	my @nplets = ();
	my @q = ();

	for my $filename (<om-leaderboard/$puzzle_path/*.solution>) {
		my @parts = solution_to_parts(slurp($filename, 1));
		my $nplet = json_to_nplet(slurp($filename =~ s/solution$/json/r));
		expand_nplet($nplet);
		push @q, [@parts, $nplet] if -M $filename < $max_age;
		push @nplets, $nplet;
	}

	my @new_nplets = ();
	my @new_filenames = ();

	while (@q) {
		my $parts = shift @q;
		my $nplet = pop @$parts;
		$CYCLE_LIMIT = $nplet->[1] + 1;
		for my $variant (variantify(@$parts)) {
			my $parts = $variant;
			my $nplet = pop @$parts;
			expand_nplet($nplet);
			my @records = get_records($nplet, \@nplets, $puzzle_type);
			my @outparetos = grep { nplet_lt($nplet, $_) } @nplets;
			next if !@records && !@outparetos;
			next if !is_pareto_anywhere($nplet, \@nplets, $puzzle_type);

			push @nplets, $nplet;
			push @q, [@$parts, $nplet];
			$SOLUTION_NAME = $records[0] // 'PARETO';
			my $solution = parts_to_solution(@$parts);
			my $filename = "$$puzzle[0]_" . nplet_to_filename(@$nplet) . '.solution';
			say "$filename : @records", 'PARETO' x !@records;
			$filename = "$ENV{HOME}/Games/solutions/$filename";
			write_file($filename, $solution, 1);

			for (grep { nplet_lt($nplet, $new_nplets[$_]) } 0..$#new_nplets) {
				next unless -f $new_filenames[$_];
				say "got outparetoed: $new_filenames[$_]";
				`mv '$new_filenames[$_]' gotoutparetoed`;
			}
			push @new_nplets, $nplet;
			push @new_filenames, $filename;
			@$_ = @$nplet for @outparetos;
		}
	}
}
