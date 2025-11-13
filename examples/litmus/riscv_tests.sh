#!/bin/bash

find -wholename "./tests/non-mixed-size/*.json" | parallel ./tools/tester.out
