#!/bin/bash

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

LITMUS=${1}.litmus
JSON=${1}.json

if [ -z "$1" ]; then
        echo -e "Missing argument"
        exit 1
elif [ ! -f $JSON ]; then
        echo -e "$1: ${RED}Missing .json file.${NC}"
        exit 2
elif [ ! -f $LITMUS ]; then
        echo -e "$1: ${RED}Missing .litmus file.${NC}"
        exit 3
elif [ -z "$(command -v herd7)" ]; then
        echo -e "$1: ${RED}Command herd7 missing.${NC}"
        exit 4
fi

ACTUAL=$(./run_test $JSON | grep -oE "(Ok|No)")
EXPECTED=$(herd7 $LITMUS | grep -oE "(Ok|No)")

if [ -z "$ACTUAL" ] ; then
        echo -e "$1: ${RED}ERROR${NC}"
elif [ "$EXPECTED" = "$ACTUAL" ]; then
        echo -e "$1: ${GREEN}PASSED${NC} (expected $EXPECTED, found $ACTUAL)"
else
        echo -e "$1: ${RED}FAILED${NC} (expected $EXPECTED, found $ACTUAL)"
fi
