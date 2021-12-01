#!/bin/sh

# Runs the tests

con="$(buildah from freqhorn-test:latest)"

buildah run --tty "$con" run_tests.sh "$@"

buildah rm "$con" > /dev/null
