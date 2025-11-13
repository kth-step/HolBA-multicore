SAMPLE_LIST=$(shell cat sample.lst)
SAMPLE_JSON=$(patsubst /opt/litmus-tests-riscv/tests/%.litmus,tests/%.json,$(SAMPLE_LIST))
SAMPLE_RES=$(patsubst /opt/litmus-tests-riscv/tests/%.litmus,tests/%.res,$(SAMPLE_LIST))

ALL_LIST=$(shell cat all.lst)
ALL_JSON=$(patsubst /opt/litmus-tests-riscv/tests/%.litmus,tests/%.json,$(ALL_LIST))
ALL_RES=$(patsubst /opt/litmus-tests-riscv/tests/%.litmus,tests/%.res,$(ALL_LIST))

LIFTER=./tools/lifter.out
EVALUATOR=./eval/evaluator.out

sample: ${SAMPLE_RES}
sample-json: ${SAMPLE_JSON}
all: ${ALL_RES}


clean: 
	@rm -f ${ALL_JSON} ${ALL_RES}


${LIFTER}: tools
	${MAKE} -C tools

${EVALUATOR}: eval
	${MAKE} -C eval

tests/%.json: /opt/litmus-tests-riscv/tests/%.litmus ${LIFTER}
	@mkdir -p $(@D)
	${LIFTER} $< $@

tests/%.res: tests/%.json ${EVALUATOR}
	@mkdir -p $(@D)
	${EVALUATOR} $< $@

.PHONY: sample all tools eval
.SECONDARY:
