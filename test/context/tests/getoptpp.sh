#!/bin/sh

# Wrapper around `getopt` which exports all options as shell variables
# Needs to be sourced, i.e. '. ./getoptpp.sh'

getoptpp() {
    # Make GNU getopt behave according to POSIX
    export POSIXLY_CORRECT=Y

    if [ $# -lt 1 ]
    then
        echo "Usage: getoptpp [-i] options..."
        echo
        echo "options... is list of option specifiers, of the following form:"
        echo "short_letter,long_name,argument_spec"
        echo
        echo " - short_letter is the single-letter version of the option"
        echo " - long_letter is the long version of the option; required"
        echo " - argument_spec is the same as getopt; ':' for a required argument,"
        echo "   '::' for an optional argument"
        echo
        echo "Unused components must still be included; 'b,,' is -b for instance"
        echo
        echo "All arguments must be given long versions"
        echo
        echo "Pass -i to ignore unknown options"
        return 1
    fi

    if [ "$1" = "-i" ]
    then
        local ignore_unknown=Y
        shift 1
    fi

    local optstring=""
    local longopts=""
    while [ $# -gt 0 ]
    do
        if [ "$1" = "--" ]
        then
            shift 1
            break
        fi
        IFS="," read short long opt_arg <<EOF
$1
EOF
        if [ -n "$short" ]
        then
            optstring="$optstring$short$opt_arg"
            local "long_$short"="$long"
        fi
        if [ -z "$long" ]
        then
            echo "$(basename $0): A long version of option -$short is required"
            return 2
        fi
        if [ -z "$opt_arg" ]
        then
            local "noarg_$long"="Y"
        fi
        local "exists_$long"="Y"

        local longopts="$longopts -l $long$opt_arg"
        shift 1
    done

    local opts="$(getopt -q $longopts -s sh -o "$optstring" -- "$@")"
    eval set -- "$opts"
    while :
    do
        local longopt=""
        if [ "$1" = "--" ]
        then
            # End of arguments
            shift
            break
        fi

        if [ "${1#--}" != "$1" ]
        then
            # Long option
            longopt="${1#--}"
        elif [ "${1#-}" != "$1" ]
        then
            # Short option
            eval "longopt=\"\${long_${1#-}}\""
            if [ -z "$longopt" -a "$ignore_unknown" != "Y" ]
            then
                # Unknown short option passed
                echo "$(basename $0): Unrecognized option '$1'"
                return 3
            fi
        fi

        eval "local exists=\"\${exists_$longopt}\""
        if [ -z "$exists" -a "$ignore_unknown" != "Y" ]
        then
            # Unknown long option passed
            echo "$(basename $0): Unrecognized option '$longopt'"
            return 3
        fi

        eval "local noarg=\"\${noarg_$longopt}\""
        if [ -n "$noarg" ]
        then
            export "opt_$longopt"="Y"
            shift 1
        else
            export "opt_$longopt"="$2"
            shift 2
        fi
        continue
    done
}
