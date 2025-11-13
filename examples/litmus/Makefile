

SAMPLE_LIST=$(shell cat sample.lst)
SAMPLE_JSON=$(patsubst /opt/litmus-tests-riscv/tests/%.litmus,tests/%.json,$(SAMPLE_LIST))
SAMPLE_RES=$(patsubst /opt/litmus-tests-riscv/tests/%.litmus,tests/%.res,$(SAMPLE_LIST))

ALL_LIST=$(shell cat all.lst)
ALL_JSON=$(patsubst /opt/litmus-tests-riscv/tests/%.litmus,tests/%.json,$(ALL_LIST))
ALL_RES=$(patsubst /opt/litmus-tests-riscv/tests/%.litmus,tests/%.res,$(ALL_LIST))

LIFTER=./tools/lifter.out
TESTER=./tools/tester.out

sample: ${SAMPLE_RES}
sample-json: ${SAMPLE_JSON}
all: ${ALL_RES}


clean: 
	@rm -f ${ALL_JSON} ${ALL_RES}

tools:
	${MAKE} -C tools

${TESTER} ${LIFTER}: tools

tests/%.json: /opt/litmus-tests-riscv/tests/%.litmus ${LIFTER}
	@mkdir -p $(dir $@)
	${LIFTER} $< $@

tests/%.res: tests/%.json ${TESTER}
	@mkdir -p $(dir $@)
	${TESTER} $< $@

.PHONY: sample all tools
.SECONDARY:
