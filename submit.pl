#!/bin/perl

use utf8;
use v5.36;
use warnings;
use LWP::UserAgent;
use HTTP::Request::Common;


$|--;
my $ua = LWP::UserAgent->new;

for my $gif_path (<output/*.{gif,mp4}>) {
	if (-s $gif_path > 10485760) {
		next if $gif_path =~ /mp4/;
		my $mp4_path = $gif_path =~ s/gif$/mp4/r;
		`ffmpeg -i '$gif_path' -movflags faststart -pix_fmt yuv420p -vf "scale=trunc(iw/2)*2:trunc(ih/2)*2" '$mp4_path'`;
		unlink $gif_path;
		$gif_path = $mp4_path;
	}
	my $solution_path = $gif_path =~ s/(gif|mp4)$/solution/r;
	warn("missing solution! $solution_path"), next if !-f $solution_path;
	my $response = $ua->post(
		'https://zlbb.faendir.com/om/submit',
		Content_Type => 'form-data',
		Content => [
			author => 'grimBOT',
			gifData => [$gif_path],
			solution => [$solution_path],
		],
	);
	if ($response->content =~ /^"(SUCCESS|NOTHING_BEATEN)"$/) {
		unlink $gif_path, $solution_path;
		warn "NOTHING BEATEN: $solution_path" if $response->content =~ /^"NOTHING_BEATEN"$/;
		print '.';
	} else {
		warn "\nSubmission failed: " . $response->content;
		warn `ls -listr '$solution_path' '$gif_path'`;
	}
}
