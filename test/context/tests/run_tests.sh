#!/bin/sh

#set -x

cd "$(realpath $(dirname $0))"

. ./common.sh

if findopt "--help" "$@" >/dev/null
then
    printhelp "--num-cpus <integer>" "The number of CPU cores to use for running tests"
    #printhelp "--dump-output" "Print the output of each test when it completes"
    #printhelp "--rm" "Cleanup the output files of each test"
    echo
    exit 1
fi

[ -z "$testoutdir" ] && testoutdir="./test_output"
mkdir -p "$testoutdir" || exit $?

numcpus="$(findopt "--num-cpus" "$@")"
[ -z "$numcpus" ] && numcpus="$(nproc)"

#opt_rm="N"
#findopt "--rm" "$@" >/dev/null && opt_rm="Y"
#opt_dump="N"
#findopt "--dump-output" "$@" >/dev/null && opt_dump="Y"

nowdate="$(date "+%H:%M_%m-%d-%Y")"
# Define/create/initialize output files
comboout="$testoutdir/test_${nowdate}_output.txt"
timeout="$testoutdir/test_${nowdate}_timing.csv"

echo "Log output of $(basename $0)" > "$comboout"
echo "Command line: $@" >> "$comboout"
echo "Number of CPUs: $(nproc)" >> "$comboout"
printf "\n\n" >> "$comboout"

echo "TestName,TimeTakenSecs" > "$timeout"

echo "~~~Running tests~~~"
echo

failedtestcount=0
failedtests=""
successfultestcount=0
#successfultests="" # Unneeded

# Number of jobs currently running
numjobs=0
runningpids=""

# Check all running test PIDs, to see if they're done, and handle their
#   completion if so.
# Returns 0 (true) if at least one test finished.
checktestsdone() {
    testsdone=0
    newpids=""
    oldifs="$IFS"
    IFS=""
    for entry in $runningpids
    do
        IFS=""
        set -- $entry
        IFS="$oldifs"
        pid="$1"; name="$2"; outfile="$3"; timefile="$4"; expectedret="$5";
        if [ ! -d "/proc/$pid" ]
        then
            wait "$pid" >/dev/null 2>&1
            ret=$?
            timetaken="$(awk '-F ' '$1 ~ /real/ {printf "%s", $2;}' "$timefile")"

            echo "Test \"$name\" completed, in ${timetaken}s"

            if [ $ret -ne $expectedret ]
            then
                echo "Test \"$name\" failed, exit code $ret"
                echo "Test \"$name\" failed, exit code $ret" >> "$comboout"
                failedtestcount=$(( $failedtestcount + 1 ))
                failedtests="$failedtests - $name\n"
            else
                echo "Test \"$name\" succeeded, exit code $ret"
                echo "Test \"$name\" succeeded, exit code $ret" >> "$comboout"
                successfultestcount=$(( $successfultestcount + 1 ))
            fi
            echo

            echo "Output for Test \"$name\":" >> "$comboout"
            cat "$outfile" >> "$comboout"
            printf "\"$name\",$timetaken\n" >> "$timeout"

            rm "$timefile" "$outfile"

            testsdone=$(( $testsdone + 1 ))
        else
            newpids="$newpids$entry"
        fi
        IFS=""
    done
    IFS="$oldifs"

    runningpids="$newpids"
    
    if [ $testsdone -ne 0 ]
    then
        numjobs=$(( $numjobs - $testsdone ))
        return 0
    else
        return 1
    fi
}

# Separates $@ by ^_ for consumption by this script
trcmd() {
    out=""
    for arg
    do
        out="$out$arg"
    done
    echo "$out"
}

# List of all registered test cases
testcases=""

# Usage: $1 = Command (delimited by US (^_)), $2 = Name, $3 = ExpectedRet
# 'Command' is not run in a shell for inconvenience.
# 'Name' must be globally-unique.
# 'ExpectedRet' is the expected numeric return code.
addtest() {
    cmd="$1"; name="$2"; expectedret="$3";
    oldifs="$IFS"
    IFS=""

    # Sanitize 'name'
    name="$(echo "$name" | tr -d '\n')"

    for testcase in $testcases
    do
        IFS=""
        set -- $testcase
        tcmd="$1"; tname="$2"; texpectedret="$3";
        if [ "$tname" = "$name" ]
        then
            echo "ERROR: Test name \"$name\" already exists." 1>&2
            exit 9
        fi
        IFS=""
    done
    IFS="$oldifs"
    testcases="${testcases}$cmd$name$expectedret"
}

if [ -z "$(ls test*.sh)" ]
then
    echo "No tests to run. Done."
fi

for testsh in $(ls test*.sh)
do
    . "./$testsh"
done

oldifs="$IFS"
IFS=""
for testcase in $testcases
do
    IFS=""
    set -- $testcase
    IFS="$oldifs"
    cmd="$1"; name="$2"; expectedret="$3";
    if [ $numjobs -eq $numcpus ]
    then
        while :
        do
            sleep 0.1s
            if checktestsdone
            then
                break
            fi
        done
    fi
    outfile="$(mktemp)"
    timefile="$(mktemp)"
    echo "Starting test \"$name\"."
    IFS=""
    set -- $cmd
    IFS="$oldifs"
    if [ -n "$(which time 2>/dev/null)" ]
    then
        # We have executable 'time'
        time -p -o "$timefile" "$@" > "$outfile" 2>&1 &
        pid=$!
    elif { time :; } >/dev/null 1>&2
    then
        # We have built-in 'time'
        { time "$@" > "$outfile" 2>&1; } 2>"$timefile" &
        pid=$!
    else
        echo "ERROR: No 'time' executable or built-in found."
        exit 10
    fi
    runningpids="$runningpids$pid$name$outfile$timefile$expectedret"
    numjobs=$(( $numjobs + 1 ))

    IFS=""
done
IFS="$oldifs"

# Wait for all tests to finish running.
while :
do
    sleep 0.1s
    checktestsdone
    if [ $numjobs -eq 0 ]
    then
        break
    fi
done

echo
echo "~~~Done running tests: $successfultestcount tests passed, $failedtestcount tests failed~~~"
echo

if [ $failedtestcount -ne 0 ]
then
    echo "~~~Failed tests~~~"
    printf "$failedtests"
fi
