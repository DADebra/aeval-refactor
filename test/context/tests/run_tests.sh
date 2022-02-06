#!/bin/sh

#set -x

cd "$(realpath $(dirname $0))"

. ./common.sh

# Handle unexpected termination
trap "kill -KILL 0" EXIT INT TERM QUIT

normexit() {
    trap - EXIT INT TERM QUIT
    exit $1
}

if findopt "--help" "$@" >/dev/null
then
    printhelp "--test <string>" "Only run the test with the given name"
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
    comboout="/dev/null"; timeout="/dev/null";
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

# Number of jobs currently running
numjobs=0
runningpids=""

# Time the execution of the command specified by "$@", outputting results to
# $1 (i.e. "$@" starts at arg 2)
timecmd() {
    outfile="$1"
    shift 1
    start="$(date +%s.%N)"
    ("$@")
    ret=$?
    end="$(date +%s.%N)"
    diff="$(echo "$end - $start" | bc)"
    if [ "${diff#.}" != "$diff" ]
    then
        # bc outputs e.g. '.8' instead of '0.8'
        diff="0$diff"
    fi
    if [ "${diff%.}" != "$diff" ]
    then
        # Busybox 'date' doesn't support %N
        diff="${diff}0"
    fi
    echo "$diff" > "$outfile"
    return $ret
}

# Check all running test PIDs, to see if they're done, and handle their
#   completion if so.
# Returns 0 (true) if at least one test finished.
checktestsdone() {
    if [ -z "$runningpids" ]
    then
        return 0
    fi
    local pid name outfile timefile expectedret parallel oldifs testsdone
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
        parallel="$6";
        if [ ! -d "/proc/$pid" ]
        then
            wait "$pid" >/dev/null 2>&1
            ret=$?
            timetaken="$(cat "$timefile")"

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
            echo
            echo "$successplain \"$name\": exit code $ret, in ${timetaken}s" >> "$comboout"

            echo "Output for \"$name\":" >> "$comboout"
            cat "$outfile" >> "$comboout"
            printf "\"$name\",$timetaken\n" >> "$timeout"

            rm "$timefile" "$outfile"

            testsdone=$(( $testsdone + $parallel ))
        else
            newpids="$newpids$entry"
        fi
        IFS=""
    done
    IFS="$oldifs"

    runningpids="$newpids"
    
    if [ $testsdone -ne 0 ]
    then
        numjobs=$(( $numjobs - $testsdone ))
        if [ $numjobs -lt 0 ]
        then
            echo "ERROR: numjobs is less than 0 ($numjobs)"
            numjobs=0
        fi
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

# Will be "yes" if --test was provided and we found the test with that name
foundruntest=""

# Usage: $1 = Command (delimited by US (^_)), $2 = Name, $3 = ExpectedRet,
#        $4 = Parallel
# 'Command' is not run in a shell for inconvenience.
# 'Name' must be globally-unique.
# 'ExpectedRet' is the expected numeric return code.
# 'Parallel' is the number of CPU cores the test will take up.
addtest() {
    if [ $# -lt 4 -o -z "$1" -o -z "$2" -o -z "$3" -o -z "$4" ]
    then
        echo "ERROR: addtest expects 4 parameters!"
        normexit 4
    fi
    cmd="$1"; name="$2"; expectedret="$3"; parallel="$4";
    oldifs="$IFS"
    IFS=""

    # Sanitize 'name'
    name="$(echo "$name" | tr -d '\n')"

    if [ -n "$runtest" -a "$name" = "$runtest" ]
    then
        foundruntest="yes"
    fi

    for testcase in $testcases
    do
        IFS=""
        set -- $testcase
        tcmd="$1"; tname="$2";
        if [ "$tname" = "$name" ]
        then
            echo "ERROR: Test name \"$name\" already exists." 1>&2
            normexit 9
        fi
        IFS=""
    done
    IFS="$oldifs"
    testcases="${testcases}$cmd$name$expectedret$parallel"
}

if [ -z "$(ls test*.sh)" ]
then
    echo "No tests to run. Done."
fi

for testsh in $(ls test*.sh)
do
    . "./$testsh"
done

if [ -n "$runtest" -a -z "$foundruntest" ]
then
    echo "Couldn't find test named \"$runtest\". Exiting."
    normexit 2
fi

oldifs="$IFS"
IFS=""
for testcase in $testcases
do
    IFS=""
    set -- $testcase
    IFS="$oldifs"
    cmd="$1"; name="$2"; expectedret="$3"; parallel="$4";

    if [ -n "$runtest" ]
    then
        if [ "$name" != "$runtest" ]
        then
            continue
        else
            timefile="$(mktemp)"
            oldifs="$IFS"
            IFS=""
            set -- $cmd
            IFS="$oldifs"
            timecmd "$timefile" "$@" 2>&1
            ret=$?
            echo "Test finished"
            echo
            echo -n "Result: "
            [ "$ret" = "$expectedret" ] && echo "${green}SUCCESS$nocolor" ||
                echo "${red}FAILED$nocolor"
            echo "Return value: $ret"
            echo -n "Time taken: "
            cat "$timefile" | tr -d '\n'
            echo "s"
            [ "$ret" = "$expectedret" ]
            normexit $?
        fi
    fi

    if [ $(( $numjobs + $parallel )) -gt $numcpus ]
    then
        while :
        do
            sleep 0.1
            if checktestsdone
            then
                break
            fi
        done
    fi
    outfile="$(mktemp)"
    timefile="$(mktemp)"
    echo "${cyan}START${nocolor} \"$name\"."; echo
    IFS=""
    set -- $cmd
    IFS="$oldifs"
    timecmd "$timefile" "$@" > "$outfile" 2>&1 &
    pid=$!
    runningpids="$runningpids$pid$name$outfile$timefile$expectedret$parallel"
    numjobs=$(( $numjobs + $parallel ))

    IFS=""
done
IFS="$oldifs"

# Wait for all tests to finish running.
while :
do
    sleep 0.1
    checktestsdone
    if [ $numjobs -eq 0 ]
    then
        break
    fi
done

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

# Cleanup our children
trap '' TERM INT QUIT EXIT
kill -INT 0
sleep 0.5
kill -TERM 0
sleep 0.5
kill -QUIT 0
