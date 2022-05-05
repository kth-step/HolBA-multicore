#!/bin/bash

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

TESTFILE=$(echo $1 | awk '{ print $1 }')
EXPECTED=$(echo $1 | awk '{ print $2 }')

if [ -z "$TESTFILE" ]; then
        echo -e "${RED}Missing argument 1, json file.${NC}"
        exit 1
elif [ -z "$EXPECTED" ]; then
        echo -e "${RED}Missing argument 2, expected results (Ok/No).${NC}"
        exit 2
fi

case $TESTFILE in
        *.json) 
                ;;
        *)
                TESTFILE=$TESTFILE.json
                ;;
esac

if [ ! -f "$TESTFILE" ]; then
        echo -e "$TESTFILE: ${RED}Could not find .json file.${NC}"
        exit 3
fi

ACTUAL=$(./run_test $TESTFILE | grep -oE "(Ok|No)")

if [ -z "$ACTUAL" ] ; then
        echo -e "$TESTFILE: ${RED}ERROR${NC}"
elif [ "$EXPECTED" = "$ACTUAL" ]; then
        echo -e "$TESTFILE: ${GREEN}PASSED${NC} (expected $EXPECTED, found $ACTUAL)"
else
        echo -e "$TESTFILE: ${RED}FAILED${NC} (expected $EXPECTED, found $ACTUAL)"
fi
