

rwildcard=$(wildcard $1$2) $(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2))

RISCV_SOURCE=/opt/litmus-tests-riscv/tests/non-mixed-size
RISCV_LITMUS=$(call rwildcard,${RISCV_SOURCE}/,*.litmus)
RISCV_JSON=$(patsubst ${RISCV_SOURCE}/%.litmus,tests/riscv/%.json,$(RISCV_LITMUS))
RISCV_RES=$(patsubst ${RISCV_SOURCE}/%.litmus,tests/riscv/%.res,$(RISCV_LITMUS))
RISCV_HERD=$(patsubst ${RISCV_SOURCE}/%.litmus,tests/riscv/%.herd,$(RISCV_LITMUS))

ARMV8_SOURCE=/opt/litmus-tests-riscv/tests/to-AArch64
ARMV8_LITMUS=$(call rwildcard,${ARMV8_SOURCE}/,*.litmus)
ARMV8_JSON=$(patsubst ${ARMV8_SOURCE}/%.litmus,tests/armv8/%.json,$(ARMV8_LITMUS))
ARMV8_RES=$(patsubst ${ARMV8_SOURCE}/%.litmus,tests/armv8/%.res,$(ARMV8_LITMUS))
ARMV8_HERD=$(patsubst ${ARMV8_SOURCE}/%.litmus,tests/armv8/%.herd,$(ARMV8_LITMUS))

LIFTER=./tools/lifter.out
TESTER=./tools/tester.out

all: riscv armv8

riscv: ${RISCV_HERD} ${RISCV_RES}

armv8: ${ARMV8_HERD} ${ARMV8_RES}

clean: 
	@rm -f ${RISCV_JSON} ${ARMV8_JSON} ${RISCV_RES} ${ARMV8_RES} ${RISCV_HERD} ${ARMV8_HERD}

tools:
	${MAKE} -C tools

${TESTER} ${LIFTER}: tools

tests/riscv/%.json: ${RISCV_SOURCE}/%.litmus ${LIFTER}
	@mkdir -p $(dir $@)
	${LIFTER} $< $@

tests/armv8/%.json: ${ARMV8_SOURCE}/%.litmus ${LIFTER}
	@mkdir -p $(dir $@)
	${LIFTER} $< $@

tests/%.res: tests/%.json ${TESTER}
	@mkdir -p $(dir $@)
	${TESTER} $< > $@

tests/riscv/%.herd: ${RISCV_SOURCE}/%.litmus
	@mkdir -p $(dir $@)
	herd7 $< > $@

tests/armv8/%.herd: ${ARMV8_SOURCE}/%.litmus
	@mkdir -p $(dir $@)
	herd7 $< > $@

.PHONY: all riscv armv8 tools
.SECONDARY:
