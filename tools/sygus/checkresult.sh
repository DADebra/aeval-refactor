#!/bin/sh

# Runs the SyGuS solver, checking the result returned with Z3 (if found)

if [ $# -ne 1 -o "$1" = "--help" ]
then
  echo "Usage: $(basename "$0") program.sl"
  echo
  echo "Runs SyGuS solver on given program, and checks the result returned"
  echo "with Z3 to ensure it's correct."
  exit 1
fi

program=""
getprog() {
  shift $(( $# - 1 ))
  program="$1"
}
getprog "$@"
program="$(realpath "$program")"

cd "$(realpath "$(dirname "$0")")"

sout="$(mktemp)"
serr="$(mktemp)"
trap "rm -f $sout $serr;" EXIT
trap "rm -f $sout $serr; kill -KILL -0;" QUIT TERM INT

../../build/tools/sygus/sygussolver "$program" > "$sout" 2> "$serr"
ret=$?
pout="$(cat "$sout")"
perr="$(cat "$serr")"
rm -f "$sout" "$serr"

if [ "$pout" = "fail" -o "$pout" = "infeasible" -o $ret -ne 0 ]
then
  echo "$perr"
  echo "$pout"
  echo "[checkresult.sh] No solution found."
  exit $ret
fi

if cat "$program" | grep -E -q 'chc-constraint|inv-constraint'
then
  echo "[checkresult.sh] Program includes chc- or inv-constraint, currently unsupported"
  exit 9
fi

# Won't work because we need ~a V ~b, not ~a /\ ~b
smtprog="$(cat "$program" | grep -E 'constraint|declare-.*|define-.*' |
  sed -r '/^\(constraint/{s/^\(constraint(.*)\)$/\1/;H;s/.*//;};${p;s/.*//;x;s/\n/ /g;s/^/\(assert \(not \(and /;s/$/\)\)\)/;s/  */ /g;}')"

z3in="$(printf "%s\n%s\n(check-sat)\n" "$pout" "$smtprog")"
z3resp="$(echo "$z3in" | z3 -in)"
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
    echo "$pout"
    exit 0
else
    echo "Faulty synthesis found:"
    echo "$pout"
    echo "SMT file:"
    echo "$z3in"
    echo
    echo "Z3 output:"
    echo "$z3in" | z3 -model -in
    exit 1
fi
