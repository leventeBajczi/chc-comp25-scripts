#!/usr/bin/env python3

import sys
import os
import yaml
import re

prefix = sys.argv[1]

def truth(verdict):
    match verdict:
        case "true":
            return True
        case "false":
            return False
        case _:
            return None

for test_results in sys.argv[2:]:
    with open(test_results, "r") as results:

        for line in results.readlines():
            if ".yml" in line or ".smt2" in line:
                entries = re.split(r'\s+', line.strip())

                if len(entries) < 2:
                    continue

                file = prefix + "/" + entries[0]

                if file.endswith(".smt2"):
                    file = file[:-5] + ".yml"

                description_yml = file
                new_verdict = entries[2]

                data = None
                update = False

                try:
                    with open(description_yml, "r") as file:
                        data = yaml.safe_load(file)
                        for property in data['properties']:
                            if property["property_file"].endswith("properties/check-sat.prp"):
                                if "expected_verdict" in property:
                                    old_verdict = property["expected_verdict"]
                                else:
                                    old_verdict = None
                                
                                if new_verdict == "true" or new_verdict == "false":
                                    new_verdict = truth(new_verdict)

                                    property["expected_verdict"] = new_verdict
                                    print("updating verdict for " + description_yml + " to " + str(new_verdict))
                                    update = True
                                else:
                                    print("keeping verdict for " + description_yml)



                    if data and update:
                        with open(description_yml, "w") as file:
                            yaml.dump(data, file)
                except e:
                    print("skipping " + description_yml + str(e))

