.PHONY: help yml

SMT2 ?= $(shell find ../chc-comp24-benchmarks -iname "*.smt2")
YML = $(SMT2:.smt2=.yml)

SOLVER ?= z3 -t:500

help:
	@echo "Please refer to README.md"

yml: $(YML)

%.yml: %.smt2
	./create-benchexec-yml.py $< $@ $(SOLVER)