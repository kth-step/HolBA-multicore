include ../../config.env.sh

export PATH := $(PATH):${HOLBA_HOL_DIR}/bin
export RISCV_CC := ${HOLBA_GCC_RISCV_PREFIX}gcc
export ARM_CC := ${HOLBA_GCC_ARM_PREFIX}gcc
export ARM8_CC := ${HOLBA_GCC_ARM8_PREFIX}gcc

SHELL=/bin/bash

.PHONY: all clean
all: lift_test run_test
clean:
	rm -f lift_test run_test *.o

.PHONY: heap
heap:
	Holmake

%.o: %.sml heap
	hol -q $< <<< "val _ = PolyML.export(\"$*\", main)" >/dev/null

lift_test: lift_test.o 
	polyc $< -o $@

run_test: run_test.o 
	polyc $< -o $@
