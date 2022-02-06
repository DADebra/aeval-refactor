#!/bin/sh

# Runs the tests. You'll want this.
#
# Set --runtime to 'buildah', 'docker', or 'host' (no container) to configure
#   how to run the tests.

testdir="$(realpath "$(dirname "$0")")"
projectroot="$(realpath "$testdir/..")"

bindir="$(realpath "$projectroot/build/tools/deep")"

. "$testdir/context/tests/common.sh"

if findopt "--help" "$@" >/dev/null
then
    echo "Usage: $(basename $0) options..."
    echo
    echo "Options:"
    printhelp "--verbose" "Be verbose with output"
    printhelp "--runtime <docker,buildah,host>" "The runtime used to run tests"
    printhelp "--out-dir <directory>" "The directory where test output will be stored"
    "$testdir/context/tests/run_tests.sh" --help
    exit 1
fi

buildah="$(which buildah)"
docker="$(which docker)"

testoutdir="$(findopt "--out-dir" "$@")"
[ -n "$testoutdir" ] && testoutdir="$(realpath "$testoutdir")"
[ -z "$testoutdir" ] && testoutdir="$projectroot/test_output"
mkdir -p "$testoutdir"
export TESTOUTDIR="$testoutdir"

cd "$testdir"

opt_runtime="$(findopt "--runtime" "$@")"
findopt "--verbose" "$@" >/dev/null && opt_verbose=Y

[ -z "$opt_runtime" ] && opt_runtime="host"

if [ "$opt_runtime" != "host" ] && ! which "$opt_runtime" >/dev/null 2>&1
then
    avail="host"
    if [ -n "$buildah" ]; then avail="$avail, buildah"; fi
    if [ -z "$docker"  ];  then avail="$avail, docker"; fi

    echo "Error: \"$opt_runtime\" requested as runtime, but not found on PATH."
    echo
    echo "Available runtimes on this host: $avail"
    exit 4
fi

if [ "$opt_runtime" = "buildah" ]
then
    echo "Building..."
    if [ -n "$opt_verbose" ]
    then
        sh ./build_buildah.sh
    else
        sh ./build_buildah.sh >/dev/null 2>&1
    fi
    echo "Running..."
    exec sh ./run_buildah.sh "$@"
elif [ "$opt_runtime" = "docker" ]
then
    echo "Building..."
    if [ -n "$opt_verbose" ]
    then
        sh ./build_docker.sh
    else
        sh ./build_docker.sh >/dev/null 2>&1
    fi
    echo "Running..."
    exec sh ./run_docker.sh "$@"
elif [ "$opt_runtime" = "host" ]
then
    export PATH="$PATH:$bindir"
    export BENCHDIR="$(realpath ../bench_horn)"
    export GRAMDIR="$(realpath ../grammars)"
    echo "Running..."
    cd ./context/tests
    exec sh ./run_tests.sh "$@"
else
    echo "Unrecognized runtime \"$opt_runtime\". Exiting." 1>&2
    exit 1
fi
