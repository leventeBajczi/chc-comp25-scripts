.PHONY: help yml

PRP ?= ../chc-comp25-benchmarks/properties/check-sat.prp
SMT2 ?= $(shell find ../chc-comp25-benchmarks/ -iname "*.smt2")
YML = $(SMT2:.smt2=.yml)

SOLVER ?= z3 -t:100

help:
	@echo "Please refer to README.md"

smt2:
	echo $(SMT2)

yml: $(YML)

%.yml: %.smt2
	./create-benchexec-yml.py $(PRP) $< $@ $(SOLVER)