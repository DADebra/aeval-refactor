#!/bin/sh

if [ $# -lt 1 ]
then
  echo "Usage: $(basename $0) freqhorn --b4simpl [args...]"
  echo
  echo "Run freqhorn, keeping track of how long each iteration takes."
  echo "Remember to run freqhorn with '--b4simpl'!"
  echo
  exit 1
fi

echo IterTimeSec

exec stdbuf -i0 -o0 "$@" | stdbuf -i0 -o0 gawk '
  @load "time";
  BEGIN { lastitertime=gettimeofday(); }
  /Before simpl/ { itertime=gettimeofday();
    printf("%.6f\n", itertime - lastitertime);
    lastitertime=itertime;
    fflush();
  }'
