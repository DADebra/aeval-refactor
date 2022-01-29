#!/bin/sh

#set -x

benches="abdu_01.smt2 abdu_02.smt2 abdu_03.smt2 abdu_04.smt2"

if [ -z "$traversalsettings" ]
then
    echo "ERROR: Must set \$traversalsettings!" 1>&2
    exit 11
fi

# Usage: $1 = CHC file to run on, $2 = traversal settings to use (space-delim)
dotravcomptest() {
    cfg="traversal_cfg.smt2"
    bench="$1"
    settings="$2"
    old="$(mktemp)"
    new="$(mktemp)"
    rm "$old" "$new"
    mkfifo "$old" "$new"
    freqhorn --v1 --attempts 500 --b4simpl --gen_method traverse $settings --grammar "$GRAMDIR/$cfg" "$BENCHDIR/$bench" | grep "Before simplification" > "$old" &
    pid1=$!
    freqhorn --v1 --attempts 500 --b4simpl --gen_method newtrav $settings --grammar "$GRAMDIR/$cfg" "$BENCHDIR/$bench" | grep "Before simplification" > "$new" &
    pid2=$!
    diff -w "$old" "$new"
    ret3=$?
    wait $pid1
    ret1=$?
    wait $pid2
    ret2=$?
    return $(( $ret1 + $ret2 + $ret3 ))
}

for bench in $benches
do
    addtest "$(trcmd dotravcomptest "$bench" "$traversalsettings")" "Test newtrav for $bench and options $traversalsettings" 0 2
done
