#!/usr/bin/env python3
import smtlib
import sys

model_file = sys.argv[1]
chc_file = sys.argv[2]
assert chc_file.endswith(".smt2")

smt_file = chc_file[:-4] + "-validate.smt2"

funs = {}

def define_funs(cmds, funs):
    for cmd in cmds:
        match cmd:
            case ("define-fun", name, *args):
                funs[name] = cmd

with open(model_file, "r") as file:
    status = file.readline().strip()
    assert status == "sat"
    content = file.read()
    model = smtlib.parse_expr(content)

    match model:
        case ("model", *cmds):
            define_funs(cmds, funs)
        case cmds:
            define_funs(cmds, funs)

with open(chc_file, "r") as file:
   content = file.read()
   cmds = smtlib.parse_exprs(content)

defs = []
clauses = []

for cmd in cmds:
    match cmd:
        case ("set-logic", "HORN"):
            defs.append(("set-logic", "ALL"))

        case ("declare-fun", name, *args):
            defs.append(funs[name])

        case ("assert", phi):
            clauses.append(phi)

        case ("check-sat", ):
            pass
        case ("get-model", ):
            pass

        case _:
            defs.append(cmd)

for cmd in defs:
    for line in smtlib.print_expr(cmd):
        print(line)

goal = ("assert", ("not", ("and", *clauses)))

for line in smtlib.print_expr(goal):
    print(line)

print("(check-sat)")