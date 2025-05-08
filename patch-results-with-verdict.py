#!/usr/bin/env python3

import sys
from lxml import etree
import bz2
import os
import yaml

xml_bz2 = sys.argv[1]

with bz2.BZ2File(xml_bz2, "r") as file:
    tree = etree.parse(file)

for run in tree.findall("run"):
    dir = os.path.dirname(xml_bz2)
    input_smt2 = dir + "/" + run.get("name")
    description_yml = input_smt2[:-5] + ".yml"
    with open(description_yml, "r") as file:
        data = yaml.safe_load(file)
        
        for property in data['properties']:
            if property["property_file"].endswith("properties/check-sat.prp"):
                if "expected_verdict" in property:
                    verdict = property["expected_verdict"]
                    if verdict is True:
                        run.set("expectedVerdict", "true")
                    if verdict is False:
                        run.set("expectedVerdict", "false")

with bz2.BZ2File(xml_bz2, "w") as file:
    tree.write(file, pretty_print=True)