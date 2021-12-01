#!/bin/sh

# Runs the tests

exec docker run --rm --interactive --tty freqhorn-test run_tests.sh "@"
