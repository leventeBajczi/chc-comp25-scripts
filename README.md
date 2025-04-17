# Scripts used in CHC-COMP 2025

## Environment

- Python3 with packages `z3-solver`, `pyyaml`
- [Benchexec](https://github.com/sosy-lab/benchexec)

## Smoke tests

1. Get benchmarks from CHC-COMP 2024

    git clone https://github.com/chc-comp/chc-comp24-benchmarks.git ../chc-comp24-benchmarks

2. Create some `*.yml` files for [benchexec](https://github.com/sosy-lab/benchexec)

    make yml # SOLVER="z3 -t:500
    make yml SOLVER="echo unknown"

