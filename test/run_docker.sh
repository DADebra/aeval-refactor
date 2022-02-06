#!/bin/sh

# Make sure we can actually connect to the docker daemon
docker version >/dev/null || exit $?

if [ -z "$TESTOUTDIR" ]
then
  echo "run_docker: Programmer error: \$TESTOUTDIR must be set"
  exit 3
fi

# Runs the tests
exec docker run --rm --interactive --tty -v "$TESTOUTDIR:/test_output" freqhorn-test run_tests.sh "@"
