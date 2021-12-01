#!/bin/sh

# Runs the tests. You'll want this.
#
# Set --runtime to 'buildah', 'docker', or 'host' (no container) to configure
#   how to run the tests.

cd "$(realpath $(dirname $0))"

. ./context/tests/getoptpp.sh
getoptpp -i h,help, ,runtime,: -- "$@"

if [ -n "$opt_help" ]
then
    echo "Usage: $(basename $0) options..."
    echo
    echo "Options for run.sh:"
    printf " --runtime <docker,buildah,host> \tThe runtime used to run tests\n"
    echo
    exit 1
fi

buildah="$(which buildah)"
docker="$(which docker)"

if [ -z "$opt_runtime" ]
then
    if [ -n "$buildah" ]
    then
        opt_runtime="buildah"
    elif [ -n "$docker" ]
    then
        opt_runtime="docker"
    else
        opt_runtime="host"
    fi
fi

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
    ./build_buildah.sh
    exec ./run_buildah.sh "$@"
elif [ "$opt_runtime" = "docker" ]
then
    ./build_docker.sh
    exec ./run_docker.sh "$@"
elif [ "$opt_runtime" = "host" ]
then
    cd ./context/tests
    exec ./run_tests.sh "$@"
else
    echo "Unrecognized runtime \"$opt_runtime\". Exiting." 1>&2
    exit 1
fi
