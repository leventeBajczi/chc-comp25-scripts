#!/usr/bin/env python3

import sys
import os
import yaml
import subprocess

property_prp = sys.argv[1]
benchmark_smt2 = sys.argv[2]
description_yml = sys.argv[3]

input_dir = os.path.dirname(description_yml)
property_file = os.path.relpath(property_prp, input_dir)
input_file = os.path.relpath(benchmark_smt2, input_dir)

property_check_sat = {
    "property_file": property_file,
}

properties = [property_check_sat]

options = {"language": "SMT-LIB"}

data = {
    "format_version": "2.0",
    "input_files": input_file,
    "properties": properties,
    "options": options,
}

cmd = sys.argv[4:]

result = subprocess.run(cmd + [benchmark_smt2], capture_output=True)
output = str(result.stdout, "utf-8")
lines = output.splitlines()
status = lines[0] if lines else "unknown"

match status:
    case "sat":
        property_check_sat["expected_verdict"] = True
    case "unsat":
        property_check_sat["expected_verdict"] = False
    case _:
        # property_check_sat["expected_verdict"] = "unknown"
        pass

with open(description_yml, "w") as file:
    yaml.dump(data, file)
