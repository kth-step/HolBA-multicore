#!/bin/bash

cat tests.lst | parallel ./tools/lifter.out
