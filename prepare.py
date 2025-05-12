#!/usr/bin/env python3

import z3
import sys
import smtlib

# warning
# - some files are in datalog format
#   top-level commands `declare-rel`, `declare-var`, `rule` without explicit quantifiers, `query`
#   also these allow define-fun, which are inlined by the current script
#   also let s are not allowed by the current format
# - some rules have top-level let

# extract
# - expected status if available
# - types used
# - functions used (?)
# - linearity of clauses
# - whether clause head uses variables only
# - whether there is a single goal query

# transform
# - transform datalog commands to smt2 commands
# - flatten clause body (conjunction only)
# - translate queries to `false` in conclusion
# - introduce variables in clause head if needed
# - merge queries if needed (CHC_COMP_FALSE)
# - introduce dummy quantified variables if none (CHC_COMP_UNUSED)
# - possibly: scramble variable names??

# write
# - category information (where?)
# - yaml
# - formatted benchmark
# - ensure a single (check-sat)
# - ensure (exit) ?
# - maybe have (get-model) and (get-proof) variants

BUILTIN = {
    "=",
    "and",
    "or",
    "=>",
    "not",
    "distinct",
    "ite",
    "<",
    "<=",
    ">",
    ">=",
    "true",
    "false",
}


def collect(sexpr, f):
    match sexpr:
        case str():
            return frozenset(f(sexpr))
        case _:
            return frozenset(x for arg in sexpr for x in collect(arg, f))


src = sys.argv[1]

lexer = smtlib.lexer()
parser = smtlib.parser()

with open(src, "r") as file:
    content = file.read()
    sexpr = parser.parse(content, lexer=lexer)
    print(sexpr)
    print(collect(sexpr, lambda x: {x} & {"Int", "Bool"}))


# Note: don't add result={} as default,
# Python shares a single instance across calls
def funs(expr, result):
    match expr:
        case (
            ("NUMERAL", _)
            | ("DECIMAL", _)
            | ("HEXADECIMAL", _)
            | ("BINARY", _)
            | ("STRING", _)
        ):
            return result

        case ("let", eqs, body):
            for var, expr in eqs:
                funs(expr, result)
            funs(body, result)
            return result

        case ("forall" | "exists", bound, body):
            funs(body, result)

        case (fun, *args):
            result.add(fun)
            for arg in args:
                funs(arg, result)
            return result


def write_expr(expr):
    match expr:
        case (
            ("NUMERAL", arg)
            | ("DECIMAL", arg)
            | ("HEXADECIMAL", arg)
            | ("BINARY", arg)
            | ("STRING", arg)
        ):
            pass


def write_command(cmd):
    match cmd:
        case ("set-logic", "HORN"):
            pass

        case ("declare-fun", name, args, "Bool"):
            pass

        case ("assert", ("forall", vars, ("=>", ("and", *body), head))):
            pass

        case ("check-sat",):
            pass

        case ("exit",):
            pass
