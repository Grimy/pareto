#!/bin/perl

use utf8;
use v5.36;
use warnings;
use JSON qw(decode_json);
use List::Util qw(min max);


$|--;

sub slurp {
	open my $fh, '<', $_[0];
	local $\; 
	<$fh>;
}

sub parse_nplets($json) {
	my @metric_names = qw(trackless cycles cost area instructions height width rate);
	my @nplets = ();
	for (@$json) {
		my $score = $_->{score};
		next if $score->{overlap};
		my @nplet = map $score->{$metric_names[$_]} // 99999, 0..$#metric_names;
		$nplet[0] = 1 - $nplet[0];
		push @nplets, \@nplet;
	}
	return @nplets;
}

my @nplets = parse_nplets(decode_json(slurp('pareto') =~ s/·|∞//gr));
my @masks = ();
my @mask_to_list = ();
my @mask_to_letters = ();

sub precompute_mask_maps() {
	my @letters = qw(T C G A I H W R);
	for my $mask (0..(2**@letters - 1)) {
		my @list = ();
		for (0..$#letters) {
			push @list, $_ if $mask & 1;
			$mask >>= 1;
		}
		push @mask_to_list, [@list];
		my $letters = join '', map $letters[$_], @list;
		push @mask_to_letters, $#list ? "($letters)" : $letters;
	}

	@masks = sort {
		my $bca = $#{$mask_to_list[$a]};
		my $bcb = $#{$mask_to_list[$b]};
		return $bca <=> $bcb if $bca != $bcb;
		return $a <=> $b;
	} (1, map { 2 * $_ } 1..127);
}

precompute_mask_maps();

sub is_superset_of_any($a, @b) {
	for (@b) {
		return 1 if ($_ & ~$a) == 0;
	}
}

sub is_pareto($this, $mask, $context) {
	my @metrics = @{$mask_to_list[$mask]};
	my @ties = ();

	for my $that (@$context) {
		my $dominated = 1;
		my $tied = 1;
		for my $metric (@metrics) {
			$tied = 0 if $that->[$metric] != $this->[$metric];
			$dominated = 0 if $that->[$metric] > $this->[$metric];
		}
		return if $dominated and not $tied;
		push @ties, $that if $tied;
	}

	return 1, @ties;
}

sub name($nplet, $context, $ban_mask) {
	my @good_masks = ();
	my @good_letters = ();
	my $future_ban_mask = 1;

	for my $mask (@masks) {
		next if is_superset_of_any($mask, @good_masks);
		next if ($mask & $ban_mask) != 0;
		my ($good, @ties) = is_pareto($nplet, $mask, $context);
		if ($good) {
			my $letters = $mask_to_letters[$mask];
			$future_ban_mask |= $mask if ($mask & ($mask - 1)) == 0;
			push @good_masks, $mask;
			if (@ties <= 1) {
				push @good_letters, $letters;
			} else {
				push @good_letters, "$letters$_" for name($nplet, \@ties, $ban_mask | $mask | $future_ban_mask);
			}
		}
	}

	return @good_letters;
}

sub compare_names($a, $b) {
	my ($a1, $b1) = map { length() - max(y/()// - 2, 0) } $a, $b;
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
		return 0 unless $+[0] >= $last_index;
		$last_index = $+[0];
	}
	return 1;
}

sub is_superstring_of_any($string, @strings) {
	for (@strings) {
		return 1 if is_substring($_, $string);
	}
}

sub prettify(@nplet) {
	my $result = "$nplet[2]g/$nplet[1]c/$nplet[3]a/$nplet[4]i/$nplet[5]h/$nplet[6]w/$nplet[7]r";
	return ($result =~ s/99999/∞/gr) . ($nplet[0] ? "" : "/T");
}

my @pretty_nplets = map {
	my @names = name($_, \@nplets, 0);
	@names = grep !is_superstring_of_any($_, @names), @names;
	@names = sort { compare_names($a, $b) } @names;
	{
		nplet => $_,
		pretty => prettify(@$_),
		names => \@names,
	}
} @nplets;

@pretty_nplets = sort {
	compare_names($$a{names}[0], $$b{names}[0])
} @pretty_nplets;

for (@pretty_nplets) {
	say "$$_{pretty}: ", join ', ', @{$$_{names}};
}
