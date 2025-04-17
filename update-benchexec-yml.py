#!/usr/bin/env python3

import sys
import os
import yaml
import re

prefix = sys.argv[1]
test_results = sys.argv[2]

def truth(verdict):
    match verdict:
        case "true":
            return True
        case "false":
            return False
        case _:
            return None

with open(test_results, "r") as results:
    for line in results.readlines():
        if line.startswith(prefix):
            entries = re.split(r'\s+', line.strip())
            description_yml = entries[0]
            new_verdict = entries[1]

            data = None
            update = False

            with open(description_yml, "r") as file:
                data = yaml.safe_load(file)
                for property in data['properties']:
                    if property["property_file"] == "../properties/check-sat.prp":
                        if "expected_verdict" in property:
                            old_verdict = property["expected_verdict"]
                        else:
                            old_verdict = None
                        
                        if new_verdict == "true" or new_verdict == "false":
                            new_verdict = truth(new_verdict)

                            if old_verdict:
                                assert old_verdict == new_verdict, "mismatching verdict" + old_verdict + " ~> " + new_verdict
                                print("keeping verdict for  ", description_yml)
                            else:
                                property["expected_verdict"] = new_verdict
                                print("updating verdict for ", description_yml)
                                update = True


            if data and update:
                with open(description_yml, "w") as file:
                    yaml.dump(data, file)
