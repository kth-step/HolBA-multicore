
RISCV_SOURCE=/opt/litmus-tests-riscv/tests/non-mixed-size
ARMV8_SOURCE=/opt/litmus-tests-armv8/tests/ifetch

RISCV_LITMUS=$(wildcard ${RISCV_SOURCE}/BASIC_2_THREAD/*.litmus)
RISCV_JSON=$(patsubst ${RISCV_SOURCE}/%.litmus,riscv/%.json,$(RISCV_LITMUS))

ARMV8_LITMUS=$(wildcard ${ARMV8_SOURCE}/BASIC_2_THREAD/*.litmus)
ARMV8_JSON=$(patsubst ${ARMV8_SOURCE}/%.litmus,armv8/%.json,$(ARMV8_LITMUS))

LIFTER=./lifter/lifter.out

.PHONY: all lifter

all: ${RISCV_JSON} ${ARMV8_JSON}

lifter:
	${MAKE} -C lifter

${LIFTER}: lifter

riscv/%.json: ${RISCV_SOURCE}/%.litmus ${LIFTER}
	@mkdir -p $(dir $@)
	ARCH=RISCV ${LIFTER} $< $@

armv8/%.json: ${ARMV8_SOURCE}/%.litmus ${LIFTER}
	@mkdir -p $(dir $@)
	ARCH=AArch64 ${LIFTER} $< $@
