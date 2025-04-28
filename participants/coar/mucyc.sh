#!/bin/bash

export LD_LIBRARY_PATH="./lib"
./main.exe -c "./config/solver/mucyc_returnF_mbp0_indNF.json" -p pcsp "$@"
