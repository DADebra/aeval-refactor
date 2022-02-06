#!/bin/sh

# Runs the tests

con="$(buildah from freqhorn-test:latest)"
trap "buildah rm $con >/dev/null" EXIT

if [ -z "$TESTOUTDIR" ]
then
  echo "run_buildah: Programmer error: \$TESTOUTDIR must be set"
  exit 3
fi

buildah run -v "$TESTOUTDIR:/test_output" --tty "$con" run_tests.sh "$@"
