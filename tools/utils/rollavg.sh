#!/bin/sh

fieldnum=1
[ -n "$1" ] && fieldnum="$1"

exec stdbuf -i0 -o0 awk -F, "
  BEGIN { avg = 0; count = 0; }
  { avg = ((avg * count) + \$$fieldnum) / (count + 1);
    count = count + 1;
    print(avg);
    fflush();
  }
"
