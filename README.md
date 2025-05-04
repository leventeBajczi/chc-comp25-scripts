# Scripts used in CHC-COMP 2025

**Warning: This repository is work in progress.**

## Environment

- Python3 with packages `z3-solver`, `pyyaml`
- [Benchexec](https://github.com/sosy-lab/benchexec)

## Smoke tests

1. Get benchmarks from CHC-COMP 2024

    git clone https://github.com/chc-comp/chc-comp24-benchmarks.git ../chc-comp24-benchmarks

2. Create some `*.yml` files for [benchexec](https://github.com/sosy-lab/benchexec)

    make yml # SOLVER="z3 -t:500
    make yml SOLVER="echo unknown"

3. Run some tools

    # ./smoke.sh chc2c-svcomp chc2c
    ./smoke.sh ChocoCatalia chococatalia
    ./smoke.sh eldarica-2.2 eldarica
    ./smoke.sh golem-x64-linux golem
    ./smoke.sh LoAT loat
    ./smoke.sh coar mucyc
    ./smoke.sh coar pcsat
    ./smoke.sh ThetaCHC theta
    ./smoke.sh UltimateTreeAutomizer ultimatetreeautomizer
    ./smoke.sh UltimateUnihorn ultimateunihorn

## Preparing the 2025 benchmarks

- new script `classify.py`
- `format.py` only translates about 1/3 of the benchmarks, data type names are not escaped if needed