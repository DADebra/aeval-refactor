#!/bin/sh

#set -x

#benches="abdu_01.smt2 abdu_02.smt2 abdu_03.smt2 abdu_04.smt2"
# How many lines to compare
comp_lines=500

if [ -z "$traversalsettings" ]
then
    echo "ERROR: Must set \$traversalsettings!" 1>&2
    exit 11
fi
if [ -z "$benches" ]
then
    echo "ERROR: Must set \$benches!" 1>&2
    exit 11
fi
if [ -z "$cfg" ]
then
    echo "ERROR: Must set \$cfg!" 1>&2
    exit 11
fi

# Usage: $1 = CHC file to run on, $2 = traversal settings to use (space-delim),
#        $3 = CFG to use
dotravcomptest() {
    bench="$1"
    settings="$2"
    cfg="$3"
    old="$(mktemp)"
    new="$(mktemp)"
    rm "$old" "$new"
    mkfifo "$old" "$new"
    freqhorn --v1 --b4simpl --gen_method traverse $settings --grammar "$GRAMDIR/$cfg" "$BENCHDIR/$bench" | grep "Before simplification" | head -n "$comp_lines" > "$old" &
    pid1=$!
    freqhorn --v1 --b4simpl --gen_method newtrav $settings --grammar "$GRAMDIR/$cfg" "$BENCHDIR/$bench" | grep "Before simplification" | head -n "$comp_lines" > "$new" &
    pid2=$!
    diffout="$(mktemp)"
    echo "Traverse output | Newtrav output" > "$diffout"
    diff -W 200 -w -y "$old" "$new" >> "$diffout"
    ret3=$?
    rm "$old" "$new"
    if [ $ret3 -ne 0 ]
    then
      cat "$diffout"
    fi
    rm "$diffout"
    wait $pid1
    ret1=$?
    wait $pid2
    ret2=$?
    return $(( $ret1 + $ret2 + $ret3 ))
}

for bench in $benches
do
    addtest "$(trcmd dotravcomptest "$bench" "$traversalsettings" "$cfg")" "Test equivalence with CFG $cfg for $bench and options $traversalsettings" 0 2
done
