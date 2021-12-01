#!/bin/sh

set -e

cd "$(realpath $(dirname $0))"

assert() {
    eval "$1" || {
        ret=$?
        echo "Failed assertion: '$1'" 1>&2
        return $ret
    }
}

. ./getoptpp.sh

! getoptpp h,,

! getoptpp ,help, -- -h

getoptpp h,help, -- -h
assert '[ -n "$opt_help" ]' || [ =]

getoptpp a,arg,: -- --arg 823
assert '[ "$opt_arg" = "823" ]' || [ =]
unset opt_arg

getoptpp a,arg,: -- -a 823
assert '[ "$opt_arg" = "823" ]' || [ =]
unset opt_arg

! getoptpp a,arg,: -- -a

! getoptpp a,arg,: -- --arg

getoptpp a,arg,:: -- -a
assert '[ -z "$opt_arg" ]' || [ =]

getoptpp a,arg,:: -- --arg
assert '[ -z "$opt_arg" ]' || [ =]

getoptpp a,arg, b,barg, -- -a -b

! getoptpp a,arg, -- -b
getoptpp -i a,arg, -- -b
