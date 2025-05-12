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
    index = None

    with open(test_results, "r") as results:

        for line in results.readlines():
            entries = re.split("\t", line.strip())

            if len(entries) < 2:
                continue

            if entries[1] == "status" and index is None:
                index = 1

            if len(entries) < 3 and index is None:
                continue

            if entries[2] == "status" and index is None:
                index = 2

            if ".yml" in line or ".smt2" in line:
                file = prefix + "/" + entries[0]

                if file.endswith(".smt2"):
                    file = file[:-5] + ".yml"

                if not file.endswith(".yml"):
                    continue

                if index is None:
                    print(entries)

                description_yml = file
                new_verdict = entries[index]

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

                                    if old_verdict == "inconsistent":
                                        print("not changing " + description_yml)
                                    elif old_verdict is not None:
                                        if old_verdict != new_verdict:
                                            property["expected_verdict"] = "inconsistent"
                                            update = True
                                            print("inconsistent verdict " + str(new_verdict) + " for " + description_yml)
                                        else:
                                            print("keeping verdict for  " + description_yml)
                                    else:
                                        property["expected_verdict"] = new_verdict
                                        print("updating verdict for " + description_yml)
                                        update = True
                                else:
                                    print("unknown result for " + description_yml + ": " + new_verdict)


                    if data and update:
                        with open(description_yml, "w") as file:
                            yaml.dump(data, file)
                except:
                    print("skipping " + description_yml)

