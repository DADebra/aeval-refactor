#!/bin/sh

# Runs each of the traversal methods, seeing if the output matches the expected.
# Uses trav_cfg.smt2 (i.e. NOT A COMPLETE TEST OF CORRECTNESS!)

for method in traverse newtrav
do
    for type in striped ordered
    do
        if [ "$type" = "striped" ]
        then
            prio_opts="sfs bfs dfs"
        else
            prio_opts="ignored"
        fi
        for priority in $prio_opts
        do
            for order in forward reverse
            do
                for direction in ltr rtl
                do
                    . ./util_run_abs_traversal_test.sh
                done
            done
        done
    done
done
