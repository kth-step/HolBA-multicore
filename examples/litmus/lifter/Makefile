include ../../../config.env.sh

PATH := $(PATH):${HOLBA_HOL_DIR}/bin

SHELL=/bin/bash

HEAP := HolBAExamples_LitmusLifter-heap

.PHONY: all clean
all: lifter.out
clean:
	rm -f lift_test.out *.o

lifter.o: lifterLib.sml	
	Holmake

lifter.out: lifter.o 
	polyc $< -o $@
