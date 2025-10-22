
RISCV_SOURCE=/opt/litmus-tests-riscv/tests/non-mixed-size
ARMV8_SOURCE=/opt/herdtools7/catalogue/aarch64/tests

RISCV_LITMUS=$(wildcard ${RISCV_SOURCE}/BASIC_2_THREAD/*.litmus)
RISCV_JSON=$(patsubst ${RISCV_SOURCE}/%.litmus,riscv/%.json,$(RISCV_LITMUS))

ARMV8_LITMUS=$(wildcard ${ARMV8_SOURCE}/*.litmus)
ARMV8_JSON=$(patsubst ${ARMV8_SOURCE}/%.litmus,armv8/%.json,$(ARMV8_LITMUS))

LIFTER=./lifter/lifter.out

.PHONY: all lifter riscv armv8

all: ${RISCV_JSON} ${ARMV8_JSON}

lifter:
	${MAKE} -C lifter

${LIFTER}: lifter

riscv/%.json: ${RISCV_SOURCE}/%.litmus ${LIFTER}
	@mkdir -p $(dir $@)
	${LIFTER} $< $@

riscv: ${RISCV_JSON}

armv8: ${ARMV8_JSON}

armv8/%.json: ${ARMV8_SOURCE}/%.litmus ${LIFTER}
	@mkdir -p $(dir $@)
	${LIFTER} $< $@
