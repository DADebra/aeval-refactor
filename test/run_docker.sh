#!/bin/sh

# Make sure we can actually connect to the docker daemon
docker version >/dev/null || exit $?

# Runs the tests
exec docker run --rm --interactive --tty freqhorn-test run_tests.sh "@"
