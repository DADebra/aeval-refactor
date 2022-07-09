#!/bin/sh

if [ -z "$__COMMON_SH__" ]; then
__COMMON_SH__=1

# Usage: $1 = option, $2 = description
printhelp() {
    tcols=$(tput cols) # Number of columns in terminal
    leftcols=$(echo "$1" | wc -c) # Number of columns taken up by left part
    rightcols=$(echo "$2" | wc -c) # Number of columns taken up by right part
    pad=$(( $tcols - $leftcols - 3 )) # Amount to pad by
    printf "  %s" "$1"
    if [ $rightcols -gt $pad ]
    then
      if [ $rightcols -gt $tcols ]
      then
        pad=$(( $rightcols + 8 ))
      else
        pad=$tcols
      fi
      printf "\n"
    fi
    printf "%*s\n" "$pad" "$2"
}

findopt() {
    tofind="$1"
    shift 1
    while [ $# -ne 0 ]
    do
        opt="$1"
        if [ "${opt%=*}" != "$opt" ]
        then
            arg="${opt#*=}"
            opt="${opt%=*}"
        else
            arg="$2"
        fi
        if [ "$opt" = "$tofind" ]
        then
            echo "$arg"
            return 0
        fi
        shift 1
    done
    return 1
}

fi
