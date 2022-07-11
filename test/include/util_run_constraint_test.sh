#!/bin/sh

benches="abdu_01.smt2 abdu_02.smt2 abdu_03.smt2 abdu_04.smt2"
cfg="constraint_cfg.smt2"

constraintline="$1"
exists="$2"
checktext="$3"

benchesfailed=""
for bench in $benches
do
    freqhorn --v1 --attempts 100 --debug --gen_method newtrav --grammar /dev/fd/4 "$bench" 4<<EOF | grep -q -m 1 "$checktext"
$(cat "$cfg")
$constraintline
(check-sat)
EOF
    ret=$?
    if [ "$exists" = "Y" -a $ret -eq 0 ] || [ "$exists" = "N" -a $ret -ne 0 ]
    then
        benchesfailed="$benchesfailed - $bench\n"
    fi
done

if [ -n "$benchesfailed" ]
then
    echo "Failed benchmarks:"
    printf "$benchesfailed"
fi
