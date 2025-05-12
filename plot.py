#!/usr/bin/env python3

import sys
from lxml import etree
import bz2
import os
import yaml
import matplotlib.pyplot as plt
import csv

import pandas as pd

category = sys.argv[1]
files = sys.argv[2:]

config = {
    "CHC2C 1.0": {"label": "CHC2C", "color": "black", "marker": "s"},
    "ChocoCatalia": {"label": "Choco Catalia", "color": "chocolate", "marker": "s"},
    "Eldarica v2.2": {"label": "Eldarica", "color": "red", "marker": "o"},
    "Golem 0.7.1": {"label": "Golem", "color": "gray", "marker": "o"},
    "MuCyc NO_VERSION_UTIL": {"label": "MuCyc", "color": "deepskyblue", "marker": "s"},
    "PCSat NO_VERSION_UTIL": {"label": "PCSat", "color": "blue", "marker": "s"},
    "ThetaCHC 6.13.2": {"label": "ThetaCHC", "color": "firebrick", "marker": "o"},
    "LoAT cac6f7584cd3e9033eea021181c0df2b5ebe6e80": {
        "label": "LoAT",
        "color": "magenta",
        "marker": "o",
    },
    "Ultimate TreeAutomizer (unknown version)": {
        "label": "U TreeAutomizer",
        "color": "orange",
        "marker": "v",
    },
    "Ultimate Unihorn (unknown version)": {
        "label": "U Unihorn",
        "color": "gold",
        "marker": "^",
    },
}

plt.xlabel("Cumulative Score (solved tasks)")
plt.ylabel("CPU time (s)")
plt.title("CHC-COMP 2025 - " + category)

for path in files:
    with open(path, newline="") as file:
        print(path)
        reader = csv.reader(file, delimiter="\t")
        tools = next(reader)
        tool = tools[2]
        style = config[tool]

        category = next(reader)

        header = next(reader)
        assert header[2] == "status"
        assert header[3] == "cputime (s)"

        data = [row for row in reader if row[3]]
        data.sort(key=lambda row: float(row[3]))

        xdata = []
        ydata = []
        score = 0

        for _, expected, verdict, cputime, *rest in data:
            if expected == verdict:
                score = score + 1
                xdata.append(score)
                ydata.append(float(cputime))

        plt.plot(xdata, ydata, **style)


plt.grid(True)
plt.yscale('log')
plt.yticks((1,10,100,1000))
plt.ylim((-200, 2000))

plt.legend()
plt.show()
