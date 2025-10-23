
RISCV_SOURCE=/opt/litmus-tests-riscv/tests/non-mixed-size
ARMV8_SOURCE=/opt/herdtools7/catalogue/aarch64/tests

RISCV_LITMUS=$(wildcard ${RISCV_SOURCE}/BASIC_2_THREAD/*.litmus)
RISCV_JSON=$(patsubst ${RISCV_SOURCE}/%.litmus,tests/riscv/%.json,$(RISCV_LITMUS))
RISCV_RES=$(patsubst ${RISCV_SOURCE}/%.litmus,results/riscv/%.res,$(RISCV_LITMUS))

ARMV8_LITMUS=$(wildcard ${ARMV8_SOURCE}/*.litmus)
ARMV8_JSON=$(patsubst ${ARMV8_SOURCE}/%.litmus,tests/armv8/%.json,$(ARMV8_LITMUS))
ARMV8_RES=$(patsubst ${ARMV8_SOURCE}/%.litmus,results/armv8/%.res,$(ARMV8_LITMUS))

LIFTER=./tools/lifter.out
TESTER=./tools/tester.out

all: ${RISCV_JSON} ${ARMV8_JSON}

tools:
	${MAKE} -C tools

${TESTER} ${LIFTER}: tools

tests/riscv/%.json: ${RISCV_SOURCE}/%.litmus ${LIFTER}
	@mkdir -p $(dir $@)
	${LIFTER} $< $@

tests/armv8/%.json: ${ARMV8_SOURCE}/%.litmus ${LIFTER}
	@mkdir -p $(dir $@)
	${LIFTER} $< $@

results/%.res: tests/%.json
	@mkdir -p $(dir $@)
	${TESTER} $< > $@

riscv: ${RISCV_RES}

armv8: ${ARMV8_RES}

.PHONY: all riscv armv8 tools
