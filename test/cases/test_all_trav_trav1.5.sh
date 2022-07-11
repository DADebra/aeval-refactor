#!/bin/sh

# Runs the two traversal methods in parallel, comparing their output for the
#   same settings.

# Uses trav2_cfg.smt2 (not "complete", but more complete than trav_cfg.smt2)

include util_run_comp_traversal_test.sh

benches="abdu_01.smt2" # Doesn't matter
cfg="trav1.5_cfg.smt2" # Doesn't matter (though this one is good to use)
extrasettings="--maxrecdepth 1" # Additional settings to apply
comp_lines=1000 # More than usual

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
                util_run_comp_traversal_test
            done
        done
    done
done
