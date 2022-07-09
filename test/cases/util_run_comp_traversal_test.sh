#!/bin/sh

#set -x

#benches="abdu_01.smt2 abdu_02.smt2 abdu_03.smt2 abdu_04.smt2"
# How many lines to compare
[ -z "$comp_lines" ] && comp_lines=500

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
    fifotest="$(mktemp)"
    rm "$old" "$new" "$fifotest"
    mkfifo "$old" "$new" "$fifotest"
    hash atexit 2>/dev/null && atexit rm -f "$old" "$new"
    # Run as separate processes (from grep) to track their exit codes
    freqhorn --v1 --no-save-lemmas --b4simpl --gen_method coro $settings --grammar "$GRAMDIR/$cfg" "$BENCHDIR/$bench" > "$old" &
    pid1=$!
    freqhorn --v1 --no-save-lemmas --b4simpl --gen_method newtrav $settings --grammar "$GRAMDIR/$cfg" "$BENCHDIR/$bench" > "$new" &
    pid2=$!
    diffold="$(mktemp)"; diffnew="$(mktemp)"
    rm "$diffold" "$diffnew"
    mkfifo "$diffold" "$diffnew"
    hash atexit 2>/dev/null && atexit rm -f "$diffold" "$diffnew"
    grep "Before simplification" "$old" | head -n "$comp_lines" > "$diffold" &
    pidhead1=$!
    grep "Before simplification" "$new" | head -n "$comp_lines" > "$diffnew" &
    pidhead2=$!
    diffout="$(mktemp)"
    hash atexit 2>/dev/null && atexit rm -f "$diffout"
    echo "Coro output | Newtrav output" > "$diffout"
    diff -W 200 -w -y "$diffold" "$diffnew" >> "$diffout"
    ret3=$?
    wait $pidhead1
    wait $pidhead2
    rm "$old" "$new"
    rm "$diffold" "$diffnew"
    if [ $ret3 -ne 0 ]
    then
      cat "$diffout"
    fi
    rm "$diffout"
    wait $pid1
    ret1=$?
    # For some reason, the return is '1' for clean exit because of fifo closing.
    [ $ret1 -eq 1 -o $ret1 -eq 141 ] && ret1=0
    wait $pid2
    ret2=$?
    [ $ret2 -eq 1 -o $ret2 -eq 141 ] && ret2=0
    finalret=$(( $ret1 + $ret2 + $ret3 ))
    if [ $finalret -ne 0 ]
    then
        echo "Coro returned $ret1, NewTrav returned $ret2, diff returned $ret3" >&2
    fi
    return $finalret
}

for bench in $benches
do
    addtest "$(trcmd dotravcomptest "$bench" "$traversalsettings" "$cfg")" "Test equivalence with CFG $cfg for $bench and options $traversalsettings" 0 2
done
