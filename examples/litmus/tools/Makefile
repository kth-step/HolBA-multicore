include ../../../config.env.sh

PATH := $(PATH):${HOLBA_HOL_DIR}/bin

SHELL=/bin/bash

HEAP := HolBAExamples_LitmusTools-heap

.PHONY: all clean
all: lifter.out tester.out
clean:
	rm -f *.out *.o

${HEAP}: 
	Holmake

%.out: %.sml
	hol -q -b ${HEAP} $< >/dev/null
