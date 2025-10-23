include ../../../config.env.sh

PATH := $(PATH):${HOLBA_HOL_DIR}/bin

SHELL=/bin/bash

HEAP := HolBAExamples_LitmusTools-heap

.PHONY: all clean ${HEAP} lifter.o
all: lifter.out tester.out
clean:
	rm -f lift_test.out *.o

tester.o lifter.o ${HEAP}: 
	Holmake

lifter.out: lifter.o 
	polyc $< -o $@

tester.out: tester.o
	polyc $< -o $@
