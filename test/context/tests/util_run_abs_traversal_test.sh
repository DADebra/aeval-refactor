#!/bin/sh

#set -x

if [ -z "$method" ]
then
    echo "ERROR: Must set \$method !" 1>&2
    exit 11
fi

if [ -z "$type" -o -z "$priority" -o -z "$order" -o -z "$direction" ]
then
    echo "ERROR: Must set \$type, \$priority, \$order, and \$direction !" 1>&2
    exit 12
fi

# Usage: $1 = traversal settings to use (space-delim), $2 = Name of "good" file,
#        $3 = traversal method to use
dotravabstest() {
    bench="abdu_01.smt2" # Doesn't matter what this is set to
    cfg="trav_cfg.smt2" # DO NOT CHANGE
    settings="$1"
    good="$2"
    method="$3"
    old="$(mktemp)"
    rm "$old"
    mkfifo "$old"
    timeout 5s freqhorn --v1 --no-save-lemmas --attempts 100 --b4simpl --gen_method $method $settings --grammar "$GRAMDIR/$cfg" "$BENCHDIR/$bench" | grep "Before simplification" > "$old" 2>&1 &
    pid=$!
    diffout="$(mktemp)"
    echo "Good output | Program output" > "$diffout"
    diff -w -y "good/$good" "$old" >> "$diffout"
    ret1=$?
    rm "$old"
    if [ $ret1 -ne 0 ]
    then
      cat "$diffout"
    fi
    rm "$diffout"
    wait $pid
    ret2=$?
    return $(( $ret1 + $ret2 ))
}

# Synthesize command line flags and name of good file
settings="--trav_type $type --trav_order $order --trav_direction $direction"
if [ "$type" = "striped" ]
then
    settings="$settings --trav_priority $priority"
fi
good="$type-$priority-$order-$direction.txt"

addtest "$(trcmd dotravabstest "$settings" "$good" "$method")" "Test traversal $method for options $settings" 0 1
