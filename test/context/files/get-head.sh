#!/bin/sh

if [ $# -lt 1 ]
then
    echo "Usage: $(basename $0) /path/to/.git"
fi

cat "$1/HEAD" | awk -F/ '{print $NF}'
