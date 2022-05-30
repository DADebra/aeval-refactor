#!/bin/sh

#set -x

cd "$(realpath $(dirname $0))"

# Must be before we import other shell scripts (so they can use it)
exitcmds=""
atexit() {
    exitcmds="${exitcmds}$(trcmd "$@")"
}

cleanup() {
    local oldifs="$IFS"
    IFS=""
    for cmd in $exitcmds
    do
        IFS=""
        set -- $cmd
        IFS="$oldifs"
        "$@"
        IFS=""
    done
}

# Handle unexpected termination
trap "cleanup; kill -KILL 0" EXIT INT TERM QUIT

normexit() {
    cleanup
    trap - EXIT INT TERM QUIT
    exit $1
}

. ./common.sh
. ./scheduler.sh

if findopt "--help" "$@" >/dev/null
then
    printhelp "--test <string>" "Only run the test with the given name,"
    printhelp "" "or tests from the provided shell script (if ending in .sh)"
    printhelp "--num-cpus <integer>" "The number of CPU cores to use for running tests"
    #printhelp "--dump-output" "Print the output of each test when it completes"
    #printhelp "--rm" "Cleanup the output files of each test"
    echo
    normexit 1
fi

if [ -z "$TESTOUTDIR" ]
then
    echo "Programmer error: \$TESTOUTDIR must be set!"
    echo "(Maybe you're invoking this script directly? Run test/run.sh instead)"
    normexit 3
fi
mkdir -p "$TESTOUTDIR" || normexit $?

numcpus="$(findopt "--num-cpus" "$@")"
[ -z "$numcpus" ] && numcpus="$(nproc)"

runtest="$(findopt "--test" "$@")"

#opt_rm="N"
#findopt "--rm" "$@" >/dev/null && opt_rm="Y"
#opt_dump="N"
#findopt "--dump-output" "$@" >/dev/null && opt_dump="Y"

nowdate="$(date "+%m-%d-%Y_%H:%M")"
# Define/create/initialize output files
if [ -z "$runtest" ]
then
    comboout="$TESTOUTDIR/test_${nowdate}_output.txt"
    timeout="$TESTOUTDIR/test_${nowdate}_timing.csv"
else
    comboout="/dev/stdout"; timeout="/dev/null";
fi

echo "Log output of $(basename $0)" > "$comboout"
echo "Command line: $@" >> "$comboout"
echo "Number of CPUs: $(nproc)" >> "$comboout"
printf "\n\n" >> "$comboout"

echo "TestName,TimeTakenSecs" > "$timeout"

# Set up terminal colors (if stdout is terminal)
red=""; green=""; yellow=""; blue=""; magenta=""; cyan=""; nocolor="";
if [ -t 1 ]
then
    start="["; nocolor="${start}0m";
    red="${start}31m"; green="${start}32m"; yellow="${start}33m";
    blue="${start}34m"; magenta="${start}35m"; cyan="${start}36m";
fi

# For start-to-end timing
starttime="$(date +%s.%N)"
echo "~~~Running tests~~~"
echo

failedtestcount=0
failedtests=""
successfultestcount=0
#successfultests="" # Unneeded

tests="$(mktemp)"
atexit rm -f "$tests"

# Callback for job starting
onteststart() {
    local jid pid outfile errfile
    jid="$1"; pid="$2"; outfile="$3"; errfile="$4";
    jobline="$(egrep "^$jid " "$tests")"
    set -- $jobline
    shift 2; local name="$@"
    echo "${cyan}START${nocolor} \"$name\"."
}

# Callback for job completion
ontestdone() {
    local jid ret timetaken outfile errfile
    jid="$1"; ret="$2"; timetaken="$3"; outfile="$4"; errfile="$5";
    jobline="$(egrep "^$jid " "$tests")"
    set -- $jobline
    local expectedret="$2"; shift 2; local name="$@";
    if [ $ret -ne $expectedret ]
    then
        success="${red}FAILED$nocolor"
        successplain="FAILED"
        failedtestcount=$(( $failedtestcount + 1 ))
        failedtests="$failedtests - $name\n"
    else
        success="${green}SUCCESS$nocolor"
        successplain="SUCCESS"
        successfultestcount=$(( $successfultestcount + 1 ))
    fi
    echo "$success \"$name\": exit code $ret, in ${timetaken}s"
    if [ "$comboout" != "/dev/stdout" -a "$comboout" != "/dev/null" ]
    then
        echo "$successplain \"$name\": exit code $ret, in ${timetaken}s" >> "$comboout"
    fi
    if grep -q -m 1 . "$outfile"
    then
        echo "Output for \"$name\":" >> "$comboout"
        cat "$outfile" >> "$comboout"
    fi
    if grep -q -m 1 . "$errfile"
    then
        echo "Error for \"$name\":" >> "$comboout"
        cat "$errfile" >> "$comboout"
    fi
    printf "\"$name\",$timetaken\n" >> "$timeout"
}

# Will be "yes" if --test was provided and we found the test with that name
foundruntest=""

# Usage: $1 = Command (delimited by US (^_)), $2 = Name, $3 = ExpectedRet,
#        $4 = Parallel
# 'Command' is run in a shell for convenience.
# 'Name' is the human-readable name of the test and should probably be unique.
# 'ExpectedRet' is the expected numeric return code.
# 'Parallel' is the number of CPU cores the test will take up.
addtest() {
    if [ $# -lt 4 -o -z "$1" -o -z "$2" -o -z "$3" -o -z "$4" ]
    then
        echo "ERROR: addtest expects 4 parameters!"
        normexit 4
    fi
    cmd="$1"; name="$2"; expectedret="$3"; parallel="$4";

    # Sanitize 'name'
    name="$(echo "$name" | tr -d '\n')"

    if [ -z "$runtest" -o "$name" = "$runtest" ]
    then
        if [ -n "$runtest" ]
        then
            foundruntest="yes"
        fi
        addjob "$cmd" "$parallel" onteststart ontestdone
        echo "$jobid $expectedret $name" >> "$tests"
    fi
}

if [ -z "$(ls test*.sh)" ]
then
    echo "No tests to run. Done."
fi

if [ -n "$runtest" -a "${runtest%.sh}" != "$runtest" ]
then
    if [ ! -e "./$runtest" ]
    then
        echo "Error: Test script \"$runtest\" not found. Exiting."
        exit 8
    fi
    runtestcopy="$runtest"
    runtest=""
    foundruntest="yes"
    . "./$runtestcopy"
else
    for testsh in $(ls test*.sh)
    do
        . "./$testsh"
    done
fi

if [ -n "$runtest" -a -z "$foundruntest" ]
then
    echo "Couldn't find test named \"$runtest\". Exiting."
    normexit 2
fi

runjobs "$numcpus"

rm "$tests"

endtime="$(date +%s.%N)"
echo
echo "~~~Done running tests: $successfultestcount tests passed, $failedtestcount tests failed~~~"
echo

if [ $failedtestcount -ne 0 ]
then
    echo "~~~Failed tests~~~"
    printf "$failedtests"
    echo
fi

timetaken="$(echo "$endtime - $starttime" | bc)"
[ "${timetaken#.}" != "$timetaken" ] && timetaken="0$timetaken"
[ "${timetaken%.}" != "$timetaken" ] && timetaken="${timetaken}0"
echo "Total time taken: $timetaken seconds"

trap '' TERM INT QUIT EXIT
cleanup

exit 0

# Cleanup our children
#kill -INT 0
#sleep 0.5
#kill -TERM 0
#sleep 0.5
#kill -QUIT 0
