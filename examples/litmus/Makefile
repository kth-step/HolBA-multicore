
RISCV_SOURCE=/opt/litmus-tests-riscv/tests/non-mixed-size
ARMV8_SOURCE=/opt/herdtools7/catalogue/aarch64/tests

RISCV_LITMUS=$(wildcard ${RISCV_SOURCE}/BASIC_2_THREAD/*.litmus)
RISCV_JSON=$(patsubst ${RISCV_SOURCE}/%.litmus,tests/riscv/%.json,$(RISCV_LITMUS))

ARMV8_LITMUS=$(wildcard ${ARMV8_SOURCE}/*.litmus)
ARMV8_JSON=$(patsubst ${ARMV8_SOURCE}/%.litmus,tests/armv8/%.json,$(ARMV8_LITMUS))

LIFTER=./tools/lifter.out
TESTER=./tools/tester.out

all: riscv.res

tools:
	${MAKE} -C tools

${TESTER} ${LIFTER}: tools

tests/riscv/%.json: ${RISCV_SOURCE}/%.litmus ${LIFTER}
	@mkdir -p $(dir $@)
	${LIFTER} $< $@

tests/armv8/%.json: ${ARMV8_SOURCE}/%.litmus ${LIFTER}
	@mkdir -p $(dir $@)
	${LIFTER} $< $@

riscv.res: ${RISCV_JSON}
	echo ${RISCV_JSON} | parallel ${TESTER}  > riscv.res

.PHONY: all riscv armv8 tools
