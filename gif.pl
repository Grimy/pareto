#!/bin/perl

use utf8;
use v5.36;
use warnings;


my $dir = `pwd`;
chomp($dir);
local $/;

for my $file (<output/*.solution>) {
	my $path = "$dir/$file";
	my $out = $path =~ s/solution$/gif/r;
	next if -f $out;

	my $mp4 = $path =~ s/solution$/mp4/r;
	next if -f $mp4;

	next if !-f $file;
	open my $fh, '<', $file or die "Can't open $file";
	binmode($fh);
	my $level = unpack 'x4C/a', <$fh>;
	$_ = `../omsim/omsim --metric 'cycles' --metric 'visual loop start cycle' --metric 'per repetition cycles' --metric 'per repetition outputs' --metric 'lexC bracket length' 'omsim/puzzles/$level.puzzle' '$file'`;
	my $cycles = /cycles is (\d+)/ ? $1 : do { `mv '$file' invalidsolutionfile`; next };
	my $length = /per repetition cycles is (\d+)/ ? $1 : 0;
	my $outputs = /per repetition outputs is (\d+)/ ? $1 : 0;
	my $brackets = /lexC bracket length is (\d+)/ ? $1 : 0;
	my $start = 0;
	my $end = $cycles + 1;

	if ($outputs) {
		$start = /start cycle is (\d+)/ ? $1 : 0;
		my $rate = $length / $outputs;
		if ($rate == 0.5 || $rate == 1) {
			$length = ($length % 8 ? 4 : 8) * ($length % 3 ? 1 : 3);
		}
		else {
			my $ratio = $outputs / $brackets;
			$ratio /= 2 if $ratio % 2 == 0 && $rate == 2;
			$length /= $ratio;
		}
		$start -= $length while $start > $cycles + $length;
		$end = $start + $length;
	}

	# next if ($end - 0.9 * $start) > 2048;
	say "$file: $start $end";
	chdir("$ENV{HOME}/.local/share/Steam/steamapps/common/Opus Magnum") or die;
	`./ModdedLightning.bin.x86_64 '$path' out='$out' start='$start' end='$end'`;
	chdir($dir) or die;
}
