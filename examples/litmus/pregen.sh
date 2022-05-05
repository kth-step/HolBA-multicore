#!/bin/bash

TESTFILE=$1

RESULT=$(herd7 $TESTFILE | grep -E "(Ok|No)")
BASENAME=$(dirname $TESTFILE)/$(basename -s .litmus $TESTFILE)

echo $BASENAME $RESULT
