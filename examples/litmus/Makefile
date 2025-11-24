ALL_LIST=$(shell cat all.lst)
ALL_JSON=$(patsubst /opt/litmus-tests-riscv/tests/%.litmus,tests/%.json,$(ALL_LIST))
ALL_RES=$(patsubst /opt/litmus-tests-riscv/tests/%.litmus,tests/%.res,$(ALL_LIST))

LIFTER=./tools/lifter.out
EVALUATOR=./eval/evaluator.out

all: ${ALL_RES}
all-json: ${ALL_JSON}


clean: 
	@rm -f ${ALL_JSON} ${ALL_RES}


${EVALUATOR}: FORCE
	${MAKE} -C eval

${LIFTER}: FORCE
	${MAKE} -C tools

tests/%.json: /opt/litmus-tests-riscv/tests/%.litmus ${LIFTER}
	@mkdir -p $(@D)
	${LIFTER} $< $@

tests/%.res: tests/%.json ${EVALUATOR}
	@mkdir -p $(@D)
	${EVALUATOR} $< $@

FORCE: ;

.PHONY: sample all sample-json all-json FORCE
.SECONDARY:
