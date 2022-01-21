#!/bin/sh

#set -x

cd "$(realpath $(dirname $0))"

. ./common.sh

if findopt "--help" "$@" >/dev/null
then
    printhelp "--num-cpus <integer>" "The number of CPU cores to use for running tests"
    printhelp "--dump-output" "Print the output of each test when it completes"
    printhelp "--rm" "Cleanup the output files of each test"
    echo
    exit 1
fi

[ -z "$testoutdir" ] && testoutdir="."

numcpus="$(findopt "--num-cpus" "$@")"
[ -z "$numcpus" ] && numcpus="$(nproc)"

opt_rm="N"
findopt "--rm" "$@" >/dev/null && opt_rm="Y"
opt_dump="N"
findopt "--dump-output" "$@" >/dev/null && opt_dump="Y"

# Use the `time` on the PATH, if present, first.
time="$(which time)"
[ -z "$time" ] && time="time"

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
        IFS="$oldifs"
        pid="${entry%%*}"
        if [ ! -d "/proc/$pid" ]
        then
                subentry="${entry#*}"
            testsh="${subentry%%*}"
                subentry="${subentry#*}"
            outfile="${subentry%%*}"
                subentry="${subentry#*}"
            timefile="${subentry%%*}"
            wait "$pid" >/dev/null 2>&1
            ret=$?

            if [ "$opt_dump" = "Y" ]
            then
                echo "Test \"$testsh\" completed. Output:"
                cat "$outfile"
            else
                echo "Test \"$testsh\" completed. Output at $outfile"
            fi

            printf "Test \"$testsh\" completion time: "
            awk '-F ' '$1 ~ /real/ {printf "%ss\n", $2;}' "$timefile"
            rm "$timefile"

            [ "$opt_rm" = "Y" ] && rm "$outfile"

            if [ $ret -ne 0 ]
            then
                echo "Test \"$testsh\" failed, exit code $ret"
                failedtestcount=$(( $failedtestcount + 1 ))
                failedtests="$failedtests - $testsh\n"
            else
                echo "Test \"$testsh\" succeeded, exit code $ret"
                successfultestcount=$(( $successfultestcount + 1 ))
            fi
            echo

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

if [ -z "$(ls test*.sh)" ]
then
    echo "No tests to run. Done."
fi

for testsh in $(ls test*.sh)
do
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
    outfile="$testoutdir/${testsh%.sh}.out"
    timefile="$testoutdir/${testsh%.sh}.time"
    echo "Starting test \"$testsh\"."
    { $time -p sh -c ". ./$testsh > \"$outfile\" 2>&1"; } 2> "$timefile" &
    runningpids="$runningpids$!$testsh$outfile$timefile"
    numjobs=$(( $numjobs + 1 ))
done

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
