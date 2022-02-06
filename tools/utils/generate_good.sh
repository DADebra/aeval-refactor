#!/bin/sh

# Invoke 'traversal.py' and parse its output to generate good files.

# This should really only need to be invoked once.

gooddir="../../test/context/tests/good"

cd "$(dirname $(realpath $0))"
gooddir="$(realpath "$gooddir")"

./traversal.py | {
    currout="" # The current output file
    skip=""
    while read line
    do
        if [ "${line#direction}" != "$line" ]
        then
            # We have a header
            skip=""

            line="$(echo "$line" | tr -d ' ' | tr ',:' '  ')"
            set -- $line
            direction="$2"; order="$4"; type="$6"; priority="$8";
            currout="$gooddir/$type-$priority-$order-$direction.txt"
            echo -n > "$currout"
            if [ "$direction" = "rtl" ]
            then
                # Just copy from the 'ltr' file but reverse lines
                sed -r 's/Before simplification: \(\[\+    ([0-3])    ([0-3])    ([0-3])\]=0\)/Before simplification: \(\[+    \3    \2    \1\]=0\)/' "$gooddir/$type-$priority-$order-ltr.txt" > "$currout"
                skip="yes"
            fi

            if [ "$order" = "reverse" ]
            then
                # Just copy from the 'forward' file but translate 0-3
                cat "$gooddir/$type-$priority-forward-$direction.txt" |
                  tr '0123' '3210' | sed -r 's/=3/=0/g' > "$currout"
                skip="yes"
            fi
        elif [ "${line#(}" != "$line" -a -z "$skip" ]
        then
            # We have an output line
            echo "$line" | sed -r 's/\(([0-3]), ([0-3]), ([0-3])\)/Before simplification: \(\[+    \1    \2    \3\]=0\)/' >> "$currout"
        fi
    done
}
