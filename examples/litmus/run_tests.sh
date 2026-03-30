#!/bin/bash

cat tests.lst | sed -e 's/.litmus/.json/g' | parallel ./eval/evaluator.out
