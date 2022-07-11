#!/bin/sh

include util_run_comp_traversal_test.sh

traversalsettings="--trav_type striped --trav_priority sfs"
util_run_comp_traversal_test
