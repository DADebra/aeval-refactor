#!/bin/sh

set -x

benches="abdu_01.smt2 abdu_02.smt2 abdu_03.smt2 abdu_04.smt2"
cfg="traversal_cfg.smt2"

traversalsettings="$1"

benchesfailed=""
for bench in $benches
do
    freqhorn --v1 --attempts 500 --debug --gen_method newtrav $traversalsettings --grammar "$cfg" > newtrav_$$.out
    freqhorn --v1 --attempts 500 --debug --gen_method traverse $traversalsettings --grammar "$cfg" > traverse_$$.out
    diff -q newtrav_$$.out traverse_$$.out
    ret=$?
    if [ $ret -ne 0 ]
    then
        benchesfailed="$benchesfailed - $bench\n"
    fi
done

if [ -n "$benchesfailed" ]
then
    echo "Failed benchmarks:"
    printf "$benchesfailed"
fi
