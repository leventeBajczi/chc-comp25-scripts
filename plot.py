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

URL="https://www.cip.ifi.lmu.de/~ernstg/chc-comp2025/"

config = {
    "CHC2C 1.0": {"label": "CHC2C", "color": "black", "marker": "s"},
    "ChocoCatalia ": {"label": "Choco Catalia", "color": "chocolate", "marker": "s"},
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
        "label": "Ultimate TreeAutomizer",
        "color": "orange",
        "marker": "v",
    },
    "Ultimate Unihorn (unknown version)": {
        "label": "Ultimate Unihorn",
        "color": "gold",
        "marker": "^",
    },
}

plt.xlabel("Cumulative Score (solved tasks)")
plt.ylabel("CPU time (s)")
plt.title("CHC-COMP 2025 - " + category)

results = []

for path in files:
    with open(path, newline="") as file:
        reader = csv.reader(file, delimiter="\t")
        tools = next(reader)
        tool = tools[2]
        style = config[tool]

        style["marker"] = "."

        _ = next(reader)

        header = next(reader)
        assert header[2] == "status"
        assert header[3] == "cputime (s)"
        assert header[4] == "walltime (s)"

        data = [row for row in reader if row[3]]
        data.sort(key=lambda row: float(row[3]))

        xdata = []
        ydata = []
        score = 0

        correct_true = 0
        correct_false = 0
        unknown_true = 0
        unknown_false = 0
        wrong_true = 0
        wrong_false = 0
        
        total_cputime = 0.0
        total_walltime = 0.0

        for _, expected, verdict, cputime, walltime, *rest in data:
            if expected == verdict:
                score += 1
                xdata.append(score)
                ydata.append(float(cputime))

            total_cputime += float(cputime)
            total_walltime += float(walltime)

            match (expected, verdict):
                case ("true", "true"):
                    correct_true += 1
                case ("false", "false"):
                    correct_false += 1
                case ("false", "true"):
                    wrong_true += 1
                case ("true", "false"):
                    wrong_false += 1
                case (_, "true"):
                    unknown_true += 1
                case (_, "false"):
                    unknown_false += 1

        plt.plot(xdata, ydata, **style)

        results.append((style["label"], path, correct_true, correct_false, unknown_true, unknown_false, total_cputime, total_walltime))

plt.grid(True)
plt.yscale('log')
plt.yticks((1,10,100,1000))

plt.legend()
plt.savefig(category + ".svg")

results.sort(key=lambda row: -row[2] - row[3])

print("""<h4><a href="%s">%s (⇒ compare results)</a></h4>

<div class="results">
        <div style="float: left">
            <img src="2025/%s.svg" height="240px" onclick="window.open(this.src)"/>
        </div>
<table>
    <tr>
        <th class="left">Tool</th>
        <th>sat</th>
        <th>unsat</th>
        <th>CPU (s)</th>
        <th>wall (s)</th>
    </tr>
""" % (URL + "test/results/" + category + ".results.table.html", category, category))

for tool, path, correct_true, correct_false, unknown_true, unknown_false, total_cputime, total_walltime in results:
    link = path[:-4] + ".html"
    print("<tr class=\"entry\">")
    print("    <td><a href=\"" + URL + link + "\">" + tool + "</a></td>")
    print("    <td>%d</td>" % correct_true)
    print("    <td>%d</td>" % correct_false)
    # print("    <td>%d</td>" % unknown_true)
    # print("    <td>%d</td>" % unknown_false)
    # print("    <td>%d</td>" % wrong_true)
    # print("    <td>%d</td>" % wrong_false)
    print("    <td>%.0f</td>" % total_cputime)
    print("    <td>%.0f</td>" % total_walltime)
    print("</tr>")
    print()

print("""</table>
    <div style="clear: both"></div>
</div>
""")