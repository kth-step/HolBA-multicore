#!/bin/bash

find -wholename "./tests/armv8/*.json" | parallel ./tools/tester.out
