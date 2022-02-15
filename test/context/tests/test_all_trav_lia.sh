#!/bin/sh

# Runs the two traversal methods in parallel, comparing their output for the
#   same settings.

# Uses lia_no_prio_cfg.smt2 (should be the best stress test)

cfg="lia_no_prio_cfg.smt2" # Doesn't matter (though this one is good to use)
extrasettings="--maxrecdepth 1" # Additional settings to apply
comp_lines=1000 # Compare more lines than usual

# The set of benchmarks we are running on. Most crashed under old bugs.
benches="abdu_01.smt2 const_mod_1.smt2 s_split_01.smt2 s_split_09.smt2
    cegar2.smt2 bouncy_three_counters_merged.smt2 const_div_1.smt2
    dillig14.smt2 dillig43.smt2 exact_iters_2.smt2 s_disj_ite_03.smt2
    s_mutants_07.smt2 s_seeds_02.smt2 s_triv_03.smt2 trex3.smt2"

traversalsettings=""
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
                traversalsettings="$extrasettings --trav_type $type --trav_order $order --trav_direction $direction"
                if [ "$type" = "striped" ]
                then
                    traversalsettings="$traversalsettings --trav_priority $priority"
                fi
                . ./util_run_comp_traversal_test.sh
            done
        done
    done
done
