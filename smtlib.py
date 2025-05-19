#!/usr/bin/env python3

import ply.lex as lex
import ply.yacc as yacc

tokens = (
    "COMMENT",
    "LPAREN",
    "RPAREN",
    "NUMERAL",
    "DECIMAL",
    "HEXADECIMAL",
    "BINARY",
    "STRING",
    "KEYWORD",
    "SYMBOL",
    "QSYMBOL",
)

t_COMMENT = r";[^\n]+\n"

t_LPAREN = r"\("
t_RPAREN = r"\)"

t_NUMERAL = r"0|[1-9][0-9]*"
t_DECIMAL = r"(0|[1-9][0-9]*)\.[0-9]+"
t_HEXADECIMAL = r"\#x[0-9a-fA-F]+"
t_BINARY = r"\#b[01]+"
t_STRING = r"\".*\""

t_KEYWORD = r":[a-zA-Z]([a-zA-Z0-9]|-)*"
t_SYMBOL = r"([a-zA-Z~!@$%&*_+=<>.?/\^]|-)([a-zA-Z0-9~!@$%&*_+=<>.?/\^]|-)*"
t_QSYMBOL = r"\|[^\|]*\|"

t_ignore = " \t\n\r"


def p_expr_numeral(p):
    "expr : NUMERAL"
    p[0] = ("NUMERAL", p[1])


def p_expr_decimal(p):
    "expr : DECIMAL"
    p[0] = ("DECIMAL", p[1])


def p_expr_hexadecimal(p):
    "expr : HEXADECIMAL"
    p[0] = ("HEXADECIMAL", p[1])


def p_expr_binary(p):
    "expr : BINARY"
    p[0] = ("BINARY", p[1])


def p_expr_string(p):
    "expr : STRING"
    p[0] = ("STRING", p[1])


def p_expr_symbol(p):
    """expr : KEYWORD
    | SYMBOL
    | QSYMBOL"""
    p[0] = p[1]


def p_expr_compound(p):
    "expr : LPAREN exprs RPAREN"
    p[0] = tuple(p[2])


def p_exprs_first(p):
    "exprs :"
    p[0] = []


def p_exprs_more(p):
    "exprs : exprs expr"
    p[1].append(p[2])
    p[0] = p[1]


def p_exprs_comment(p):
    "exprs : exprs COMMENT"
    p[0] = p[1]


def t_error(t):
    raise ValueError("Illegal character '%s'" % t.value[0])


def p_error(p):
    print("Syntax error in input!")


def lexer():
    return lex.lex()


def parser():
    return yacc.yacc(start="exprs")


def parse_expr(text):
    lexer = lex.lex()
    parser = yacc.yacc(start="expr")
    return parser.parse(text, lexer=lexer)


def parse_exprs(text):
    lexer = lex.lex()
    parser = yacc.yacc(start="exprs")
    return parser.parse(text, lexer=lexer)


def print_expr(expr):
    match expr:
        case ("NUMERAL" | "DECIMAL" | "HEXADECIMAL" | "BINARY", num):
            return [num]
        case ("STRING", text):
            return ['"' + text + '"']
        case str():
            return [expr]
        case exprs:
            return format([line for expr in exprs for line in print_expr(expr)])

def format(args):
    if not args:
        return ["()"]

    m = max(len(arg) for arg in args)
    s = sum(len(arg) for arg in args)

    b = len(args) >= 2 and (m >= 40 or s >= 80)

    if b:
        x = "(" + args[0]
        ys = ["  " + arg for arg in args[1:-1]]
        z = "  " + args[-1] + ")"
        return [x, *ys, z]
    else:
        x = " ".join(args)
        return ["(" + x + ")"]