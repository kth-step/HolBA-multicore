include ../../../config.env.sh

PATH := $(PATH):${HOLBA_HOL_DIR}/bin

HOL_FILES=$(wildcard *Lib.sml)

SHELL=/bin/bash

HEAP := HolBAExamples_LitmusTools-heap

.PHONY: all clean
all: lifter.out
clean:
	rm -f *.out *.o

${HEAP}: FORCE
	Holmake

%.out: %.sml ${HEAP}
	hol -q -b ${HEAP} $< >/dev/null

FORCE: ;
