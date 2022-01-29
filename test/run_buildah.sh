#!/bin/sh

# Runs the tests

con="$(buildah from freqhorn-test:latest)"
trap "buildah rm $con >/dev/null" EXIT

buildah run --tty "$con" run_tests.sh "$@"
