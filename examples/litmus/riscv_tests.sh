#!/bin/bash

find -wholename "./tests/riscv/*.json" | parallel ./tools/tester.out
