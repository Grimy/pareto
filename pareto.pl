#!/bin/perl -sl

use utf8;
use v5.36;
use warnings;
use Memoize;
use JSON qw(decode_json);
use List::Util qw(min max any all);


our ($h, $j, $g, $s, $n);

sub slurp($filename) {
	open my $fh, '<', $filename;
	local $\; 
	return <$fh>;
}

sub wget($url, $filename, $force = 0) {
	$url =~ y/\\'//;
	$filename =~ y/\\'//;
	`wget '$url' -O '$filename'` unless -f $filename and not $force;
}

sub parse_nplet($score) {
	my @nplet = $score->@{qw(trackless cycles cost area instructions height width rate)};
	$nplet[0] = 1 - $nplet[0];
	$nplet[7] //= 99999;
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
		my @bca = mask_to_list($a);
		my @bcb = mask_to_list($b);
		return @bca <=> @bcb if @bca != @bcb;
		return $a <=> $b;
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

sub name($nplet, $context, $ban_mask = 0) {
	return "" if @$context <= 1;

	my @good_masks = ();
	my @good_names = ();
	my $future_ban_mask = 1;

	for my $mask (get_masks()) {
		next if is_superset_of_any($mask, @good_masks);
		next if ($mask & $ban_mask) != 0;
		my ($good, @ties) = is_pareto($nplet, $mask, $context);
		if ($good) {
			my $letters = mask_to_letters($mask);
			$future_ban_mask |= $mask if ($mask & ($mask - 1)) == 0;
			push @good_masks, $mask;
			push @good_names, "$letters$_" for name($nplet, \@ties, $ban_mask | $mask | $future_ban_mask);
		}
	}

	return @good_names;
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
	return any { is_substring($_, $string) } @strings;
}

########
# Main #
########
if ($h) {
	say "-j: update data.json";
	say "-g: update gifs";
	say "-s: update solution files";
	say "-n: update names";
	exit;
}

wget('https://zlbb.faendir.com/om/puzzle/P007/records\?includeFrontier=true', 'data.json', $j);

if ($n or $g or $s) {
	my $json = decode_json(slurp('data.json') =~ s/·|∞//gr);
	my @solves = grep { !$_->{score}->{overlap} } @$json;
	my @nplets = map {
		my $short_name = $_->{fullFormattedScore} =~ s/\///gr;
		wget($_->{gif}, "gif/$short_name.gif") if $g;
		wget($_->{solution}, "solution/$short_name.solution") if $s;
		parse_nplet($_->{score})
	} @solves;

	if ($n) {
		open my $fh, '>', 'names.txt';
		print $fh "$solves[$_]{fullFormattedScore}: ", join ' ', name($nplets[$_], \@nplets) for 0..$#nplets;
	}
}

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
	# say "$_: ", join ', ', @{$names{$_}};
}
