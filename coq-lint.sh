#!/bin/bash
set -e
## A simple shell script checking for some common Coq issues.
## Taken from https://gitlab.mpi-sws.org/iris/examples/-/blob/ffb30f920932924f37bf19f00d91dfd5e94d4c52/coq-lint.sh

FILE="$1"

if egrep -n '^\s*((Existing\s+|Program\s+|Declare\s+)?Instance|Arguments|Remove|Hint\s+(Extern|Constructors|Resolve|Immediate|Mode|Opaque|Transparent|Unfold)|(Open|Close)\s+Scope|Opaque|Transparent)\b' "$FILE"; then
    echo "ERROR: $FILE contains 'Instance'/'Arguments'/'Hint' or another side-effect without locality (see above)."
    echo "Please add 'Global' or 'Local' as appropriate."
    echo
    exit 1
fi
