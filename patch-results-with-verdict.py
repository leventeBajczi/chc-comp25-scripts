#!/usr/bin/env python3

import sys
from lxml import etree
import bz2
import os
import yaml

updated = False
xml_bz2 = sys.argv[1]

with bz2.BZ2File(xml_bz2, "r") as file:
    tree = etree.parse(file)

for run in tree.findall("run"):
    try:
        dir = os.path.dirname(xml_bz2)
        name = run.get("name")

        if name.endswith(".smt2"):
            name = name[:-5] + ".yml"

        description_yml = os.path.normpath(dir + "/" + name)

        with open(description_yml, "r") as file:
            data = yaml.safe_load(file)
            run.set("name", name)
            
            for property in data['properties']:
                if property["property_file"].endswith("properties/check-sat.prp"):
                    status = run.find('column[@title="status"]')
                    category = run.find('column[@title="category"]')

                    solved = status.get("value")

                    if "expected_verdict" in property:
                        expected = property["expected_verdict"]

                        if expected is True:
                            updated = True
                            run.set("expectedVerdict", "true")
                            print("expected true: " + description_yml)

                            if solved == "true":
                                print("correct true: " + description_yml)
                                category.set("value", "correct")
                            elif solved == "false":
                                print("wrong true: " + description_yml)
                                category.set("value", "wrong")

                        elif expected is False:
                            updated = True
                            run.set("expectedVerdict", "false")
                            print("expected false: " + description_yml)

                            if solved == "false":
                                print("correct false: " + description_yml)
                                category.set("value", "correct")
                            elif solved == "true":
                                print("wrong false: " + description_yml)
                                category.set("value", "wrong")

                        elif expected == "inconsistent":
                            run.attrib.pop("expectedVerdict")
                            print("inconclusive: " + description_yml)

                            if solved == "false" or solved == "true":
                                category.set("value", "missing")

                        else:
                            print("no change for: " + description_yml)

                    else:
                        print("no expected verdict for: " + description_yml)
                else:
                    print("skipping property for: " + description_yml)


    except Exception as e:
        print("oops: " + description_yml + " " + str(e))

if updated:
    with bz2.BZ2File(xml_bz2, "w") as file:
        tree.write(file, pretty_print=True)