#!/bin/sh

if [ $# -lt 1 ]
then
    echo "Usage: $(basename "$0") [freqhorn opts...] benchmark"
    echo
    echo "Runs freqhorn with the given options on the given benchmark,"
    echo "checking the invariant it returns with Z3"
    exit 7
fi

utilsdir="$(realpath "$(dirname "$0")")"
[ -z "$FREQHORN" ] && FREQHORN="$utilsdir/../../build/tools/deep/freqhorn"
if [ ! -x "$FREQHORN" ]
then
    echo "ERROR: Couldn't find freqhorn at \"$FREQHORN\"."
    echo "  Please set the environment variable \$FREQHORN correctly."
    exit 10
fi
z3="$utilsdir/../../build/run/bin/z3"
if [ ! -x "$z3" ]
then
    z3="$(which z3 2>/dev/null)"
    if [ ! -x "$z3" ]
    then
        echo "ERROR: This script requires a Z3 binary!"
        exit 8
    fi
fi

bench=""
getbench() {
  shift $(( $# - 1 ))
  bench="$1"
}
getbench "$@"

# Parallel-safe serialization of benchmark to chc.smt2
chcfile="$(mktemp)"
trap "rm -f $chcfile" EXIT
trap "rm -f $chcfile ; kill -KILL 0" INT TERM QUIT KILL
touch chc.smt2
(
  flock 9
  timeout -s KILL 5s "$FREQHORN" --serialize "$bench"
  ret=$?
  if [ $ret -ne 0 ]
  then
      echo "Hang while trying to serialize CHC. Exiting."
      exit $ret
  fi
  mv chc.smt2 "$chcfile"
  exit 0
) 9>>chc.smt2
ret=$?
[ $ret -ne 0 ] && exit 9

invdef="$("$FREQHORN" "$@" | awk -F% -v doprint=0 '$1 ~ /define-fun/ {doprint=1;} {if (doprint) {print $1;}}')"
if [ -n "$invdef" ]
then
    z3in="$(cat "$chcfile" | grep -v -e 'declare-fun' -e 'check-sat' -e 'set-logic' | sed -r -n 'x;/./{x;/^\(assert|\(check-sat/!{H;d;}; x;s/(\n|\t)/ /g;s/  */ /g;p;s/.*//;}; x; /^\(assert/{H;d;}; p;' |
      sed -r 's/^\(assert (.*)\)$/(push)(assert (not \1))(check-sat)(pop)/' | { echo "$invdef"; cat; })"
    rm "$chcfile"
    z3resp="$( echo "$z3in" | "$z3" -in)"
    if echo "$z3resp" | grep -q 'error'
    then
        echo "Z3 error"
        echo "SMT file:"
        echo "$z3in"
        echo
        echo "Z3 output:"
        echo "$z3resp"
        exit 11
    elif ! echo "$z3resp" | grep -q -e '^sat$'
    then
        echo "Safe invariant found:"
        echo "$invdef"
        exit 0
    else
        echo "Faulty invariant found:"
        echo "$invdef"
        echo "SMT file:"
        echo "$z3in"
        echo
        echo "Z3 output:"
        echo "$z3resp"
        exit 1
    fi
else
    echo "No invariant found"
    exit 0
fi
