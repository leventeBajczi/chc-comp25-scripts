#!/usr/bin/env python3

import z3
import sys
import smtlib


def unquote(sym):
    if sym[0] == "|" and sym[-1] == "|":
        return sym[1:-1]
    else:
        return sym


def flatten(phi):
    match phi:
        case ("and", *args):
            return [phi for arg in args for phi in flatten(arg)]
        case _:
            return [phi]

def is_linear(phis, predicates):
    n = 0
    linear = True

    # does not catch predicates inside lets
    for phi in phis:
        match phi:
            case (fun, *args) if unquote(fun) in predicates:
                n = n + 1
                if n > 1:
                    linear = False
            case _:
                pass

    return linear

def classify(cmds):
    linear = True
    predicates = set()
    features = set()

    def add_type(typ):
        match typ:
            case "Bool":
                pass
            case "Int":
                features.add("LIA")
            case "Real":
                features.add("LRA")
            case ("Array", _, _):
                features.add("Arrays")
            case ("_", "BitVec", _):
                features.add("BV")

    for cmd in cmds:
        match cmd:
            case ("declare-var", name, typ):
                add_type(typ)

            case ("declare-datatypes", decls, defs):
                features.add("ADT")
                for constrs in defs:
                    for constr, *sels in constrs:
                        for sel, typ in sels:
                            add_type(typ)

            case ("declare-rel", name, args):
                predicates.add(unquote(name))
                for typ in args:
                    add_type(unquote(typ))

            case ("declare-fun", name, args, "Bool"):
                predicates.add(unquote(name))
                for typ in args:
                    add_type(unquote(typ))

            case ("assert", ("forall", bound, ("=>", body, head))):
                linear = linear and is_linear(body, predicates)
                for var, typ in bound:
                    add_type(unquote(typ))

    if features == {"LIA"} and linear:
        return "LIA-Lin"

    elif features == {"LIA"}:
        return "LIA"

    elif features == {"LIA", "Arrays"} and linear:
        return "LIA-Lin-Arrays"

    elif features == {"LIA", "Arrays"}:
        return "LIA-Arrays"

    elif features == {"ADT"}:
        return "ADT-LIA"

    elif features == {"LIA", "ADT"}:
        return "ADT-LIA"

    elif features == {"LIA", "ADT", "Arrays"}:
        return "ADT-LIA-Arrays"

    elif features == {"LRA"} and linear:
        return "LRA-Lin"

    elif features == {"LRA"}:
        return "LRA"

    elif features == {"BV"}:
        return "BV"

    else:
        return "MIXED", features # XXX: causes file.write to crash (not str)


if __name__ == "__main__":
    src = sys.argv[1]

    lexer = smtlib.lexer()
    parser = smtlib.parser()

    with open(src, "r") as file:
        content = file.read()
        cmds = parser.parse(content, lexer=lexer)

    category = classify(cmds)

    if len(sys.argv) > 2:
        dst = sys.argv[2]

        with open(dst, "w") as file:
            file.write(category)
    else:
        print(category)
