#!/bin/bash

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

LITMUS=${1}.litmus
JSON=${1}.json

if [ -f $JSON ]; then
        echo -e "${1}: ${YELLOW}Skipping.${NC}"
        exit 1
fi

if [ ! -f $LITMUS ]; then
        echo -e "${1}: ${RED}Missing litmus file.${NC}"
        exit 2
fi

./lift_test $LITMUS $JSON >/dev/null 2>&1

if [ -f $JSON ]; then
        echo -e "${1}: ${GREEN}Lifted.${NC}"
else
        echo -e "${1}: ${RED}Lift failed.${NC}"
        exit 3
fi
