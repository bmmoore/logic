#!/bin/sh
for f in $1/*.maude; do
  echo $f;
  # Matches the expected answer and running time comment lines
  # from both the Harrison and TPTP-derived benchmarks of
  # the Maude RTP ( http://maude.cs.uiuc.edu/tools/rtp/ )
  grep 'cpu\|Answer\|Harrison' $f;
  MaudeExample $f;
done
