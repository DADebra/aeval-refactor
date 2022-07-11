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

include() {
    header="$1"
    if [ -e "$header" ]
    then
        foundheader="$header"
    elif [ -e "$INCLUDE_DIR/$header" ]
    then
        foundheader="$INCLUDE_DIR/$header"
    else
        echo "Error, couldn't include '$header'" 1>&2
        exit 4
    fi
    . "$foundheader"
}

# Fractional seconds since UNIX epoch
gettime() {
    time="$EPOCHREALTIME"
    if [ -n "$time" ]
    then
        echo "$time"
        return 0
    fi

    if hash gdate >/dev/null 2>&1
    then
        date="gdate"
    elif hash date >/dev/null 2>&1
    then
        date="date"
    else
        echo "No date command found" 1>&2
        exit 11
    fi

    time="$("$date" +%s.%N)"
    if [ "${time%.}" != "$time" ]
    then
        time="${time}0"
    fi
    echo "$time"
    return 0
}

# Compute $1 - $2
difftime() {
    difftime="$(echo "$1 - $2" | bc)"
    [ "${difftime#.}" != "$difftime" ] && difftime="0$difftime"
    [ "${difftime%.}" != "$difftime" ] && difftime="${difftime}0"
    echo "$difftime"
}

haveatexit() { hash atexit >/dev/null 2>&1; return $?; }

fi
