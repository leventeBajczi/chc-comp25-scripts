#!/bin/bash

export LD_LIBRARY_PATH="./lib"
./main.exe -c "./config/solver/pcsat_chc_comp_tbq_ar.json" -p pcsp "$@"
