#!/usr/bin/env python3

# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

import sys

from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import List, Optional

from parsy import regex, string, whitespace, eof, generate, alt, forward_declaration, from_enum


@dataclass
class Type:
    def toSmtlib(self):
        "Print type in SMTLIB format"
        raise NotImplementedError()


@dataclass
class BooleanType(Type):
    def toSmtlib(self):
        return "Bool"


@dataclass
class IntegerType(Type):
    def toSmtlib(self):
        return "Int"


@dataclass
class RationalType(Type):
    def toSmtlib(self):
        return "Real"


@dataclass
class StringType(Type):
    def toSmtlib(self):
        return "String"


@dataclass
class BitvectorType(Type):
    width: int

    def toSmtlib(self):
        return f"(_ BitVec {self.width})"


@dataclass
class FloatType(Type):
    exponent: int
    significand: int

    def toSmtlib(self):
        return f"(_ FloatingPoint {self.exponent} {self.significand})"


@dataclass
class ArrayType(Type):
    index: Type
    element: Type

    def toSmtlib(self):
        return f"(Array {self.index.toSmtlib()} {self.element.toSmtlib()})"


@dataclass
class FunctionType(Type):
    arguments: List[Type]
    value: Type

    def toSmtlib(self):
        return f"({' '.join([arg.toSmtlib() for arg in self.arguments])}) {self.value.toSmtlib()}"


# TODO Simplify grammar and make sure it matches the parser rules
"""
Grammar:

program ::= line+
line ::= ws* (definition | statement) ";\n"
definition ::= "var" ws* variable ws* "=" ws* statement
statement ::= variable ("." variable "(" ws* args ws* ")")+
args ::= arg ws* ("," ws* arg)*
arg ::= variable | boolean | integer | float | string

boolean ::= "true" | "false"
integer ::= -?[0-9]+L? | "new" ws* "BigInteger(\"" -?[0-9]+ "\")"
float ::= ...
string ::= "\"" .* "\""
"""

litInt = (regex(r"-?[0-9]+").map(int) << string("L").optional() |
          string("new") >> whitespace >> string("BigInteger(") >> whitespace.optional() >>
          regex(r'"-?[0-9]+"').map(lambda str: int(str[1:-1]))
          << whitespace.optional() << string(")"))


def test_integer():
    assert litInt.parse('123') == 123
    assert litInt.parse('-123') == -123
    assert litInt.parse('123L') == 123
    assert litInt.parse('new BigInteger("123")') == 123


litBool = string("true").map(lambda str: True) | string("false").map(lambda str: False)


def test_bool():
    assert litBool.parse('true') == True
    assert litBool.parse('false') == False


litString = string('"') >> regex(r'[^"]*') << string('"')


def test_string():
    assert litString.parse('"str"') == "str"


litType = forward_declaration()

litBoolType = string("FormulaType.BooleanType").map(lambda str: IntegerType())
litIntegerType = string("FormulaType.IntegerType").map(lambda str: IntegerType())
litRationalType = string("FormulaType.RationalType").map(lambda str: RationalType())
litStringType = string("FormulaType.StringType").map(lambda str: StringType())


@generate
def litBitvectorType():
    yield string("FormulaType.getBitvectorTypeWithSize(") >> whitespace.optional()
    width = yield regex(r'[0-9]+').map(int)
    yield whitespace.optional() << string(")")
    return BitvectorType(width)


@generate
def litFloatType():
    yield string("FormulaType.getBitvectorTypeWithSize(") >> whitespace.optional()
    exponent = yield regex(r'[0-9]+').map(int)
    yield whitespace.optional() << string(",") << whitespace.optional()
    significand = yield regex(r'[0-9]+').map(int)
    yield whitespace.optional() << string(")")
    return FloatType(exponent, significand)


@generate
def litArrayType():
    yield string("FormulaType.getArrayType(")
    yield whitespace.optional()
    index = yield litType
    yield whitespace.optional() >> string(",") >> whitespace.optional()
    elements = yield litType
    yield whitespace.optional() >> string(")")
    return ArrayType(index, elements)


litType.become(
    alt(litBoolType, litIntegerType, litRationalType, litStringType, litBitvectorType, litFloatType, litArrayType))


def test_sort():
    assert litType.parse("FormulaType.BooleanType") == IntegerType()
    assert litType.parse("FormulaType.IntegerType") == IntegerType()
    assert litType.parse("FormulaType.getBitvectorTypeWithSize(8)") == BitvectorType(8)
    assert (litType.parse("FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.IntegerType)")
            == ArrayType(IntegerType(), IntegerType()))


class Solvers(Enum):
    OPENSMT = "SolverContextFactory.Solvers.OPENSMT"
    MATHSAT5 = "SolverContextFactory.Solvers.MATHSAT5"
    SMTINTERPOL = "SolverContextFactory.Solvers.SMTINTERPOL"
    Z3 = "SolverContextFactory.Solvers.Z3"
    PRINCESS = "SolverContextFactory.Solvers.PRINCESS"
    BOOLECTOR = "SolverContextFactory.Solvers.BOOLECTOR"
    CVC4 = "SolverContextFactory.Solvers.CVC4"
    CVC5 = "SolverContextFactory.Solvers.CVC5"
    YICES2 = "SolverContextFactory.Solvers.OPENSMT"
    BITWUZLA = "SolverContextFactory.Solvers.OPENSMT"


litSolvers = from_enum(Solvers)


class ProverOptions(Enum):
    GENERATE_MODELS = "SolverContext.ProverOptions.GENERATE_MODELS"
    GENERATE_ALL_SAT = "SolverContext.ProverOptions.GENERATE_ALL_SAT"
    GENERATE_UNSAT_CORE = "SolverContext.ProverOptions.GENERATE_UNSAT_CORE"
    GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS = "SolverContext.ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS"
    ENABLE_SEPARATION_LOGIC = "SolverContext.ProverOptions.ENABLE_SEPARATION_LOGIC"


litProverOptions = from_enum(ProverOptions)


def test_proverOptions():
    assert litProverOptions.parse("SolverContext.ProverOptions.GENERATE_MODELS") == ProverOptions.GENERATE_MODELS


variable = regex(r"[A-Za-z][A-Za-z0-9]*")


def test_variable():
    assert variable.parse("var1") == "var1"
    assert variable.parse("mgr") == "mgr"


argument = litBool | litInt | litString | litType | litSolvers | litProverOptions | variable


@dataclass
class Call:
    fn: str
    args: Optional[List] = None


@generate
def call():
    yield string(".")
    fn = yield variable
    yield string("(")
    yield whitespace.optional()
    arg0 = yield argument.optional().map(lambda p: [p] if p is not None else [])
    args = []
    if (arg0 is not []):
        args = yield (whitespace.optional() >> string(",") >> whitespace.optional() >> argument).many()
    yield whitespace.optional()
    yield string(")")
    return Call(fn, arg0 + args)


@generate
def stmt():
    call0 = yield variable.map(lambda str: Call(str))
    calls = yield call.many()
    return [call0] + calls


def test_stmt():
    assert stmt.parse("var1.method(123, false)") == [Call("var1"), Call("method", [123, False])]
    assert (stmt.parse('mgr.getBitvectorFormulaManager().makeBitvector(8, new BigInteger("0"))')
            == [Call("mgr"), Call("getBitvectorFormulaManager", []), Call("makeBitvector", [8, 0])])


@dataclass
class Definition:
    variable: Optional[str]
    value: List[Call]

    def getCalls(self):
        "Project the call chain on the right to just the method names"
        return [call.fn for call in self.value]


@generate
def definition():
    yield string("var")
    yield whitespace.optional()
    var = yield variable
    yield whitespace.optional()
    yield string("=")
    yield whitespace.optional()
    value = yield stmt
    return Definition(var, value)


line = whitespace.optional() >> (definition | stmt.map(lambda p: Definition(None, p))) << string(";\n")


def test_line():
    assert (line.parse(
        'var var5 = mgr.getBitvectorFormulaManager().makeBitvector(8, new BigInteger("0"));\n')
            == Definition("var5",
                          [Call(
                              "mgr"),
                              Call(
                                  "getBitvectorFormulaManager",
                                  []),
                              Call(
                                  "makeBitvector",
                                  [8,
                                   0])]))


program = line.many() << whitespace.optional() << eof


def test_program():
    assert (program.parse(
        """
        var var5 = mgr.getBitvectorFormulaManager().makeBitvector(8, new BigInteger("0"));
        var var6 = mgr.getBitvectorFormulaManager().extend(var5, 24, false);
        var var8 = mgr.getBitvectorFormulaManager().equal(var6, var6);
        var var9 = mgr.getBitvectorFormulaManager().makeBitvector(32, 1L);
        var2.push();
        var var21 = var2.addConstraint(var8);
        var var22 = var2.isUnsat();
        var var23 = var2.getModel();
        var23.close();
        """)
            == [Definition("var5",
                           [Call("mgr"), Call("getBitvectorFormulaManager", []), Call("makeBitvector", [8, 0])]),
                Definition("var6",
                           [Call("mgr"), Call("getBitvectorFormulaManager", []), Call("extend", ["var5", 24, False])]),
                Definition("var8",
                           [Call("mgr"), Call("getBitvectorFormulaManager", []), Call("equal", ["var6", "var6"])]),
                Definition("var9",
                           [Call("mgr"), Call("getBitvectorFormulaManager", []), Call("makeBitvector", [32, 1])]),
                Definition(None, [Call("var2"), Call("push", [])]),
                Definition("var21", [Call("var2"), Call("addConstraint", ["var8"])]),
                Definition("var22", [Call("var2"), Call("isUnsat", [])]),
                Definition("var23", [Call("var2"), Call("getModel", [])]),
                Definition(None, [Call("var23"), Call("close", [])])])


def test_toSmtlib():
    assert (ArrayType(IntegerType(), ArrayType(BitvectorType(32), FloatType(8, 24))).toSmtlib()
            == "(Array Integer (Array (_ BitVec 32) (_ FloatingPoint 8 24)))")


def printBitvector(width, value):
    "Print a bitvector literal in SMTLIB format"
    digits = format(value, f'0{width}b')
    if value < 0:
        # Convert to 2s complement
        digits = ''.join(['0' if l == '1' else '1' for l in digits])
        digits = format(int(digits, 2) + 1, f'0{width}b')
    return '#b' + digits


def test_printBitvector():
    assert printBitvector(8, 5) == "#b00000101"
    assert printBitvector(8, -5) == "#b11111011"


def flattenProvers(prog: List[Definition]):
    "Push all assertions onto the same global prover"
    # We assume that the provers are not used "in parallel"
    # FIXME Reorder the instructions to avoid overlapping prover instances
    active = ""
    levels = 0
    trace = []
    for stmt in prog:
        if (stmt.getCalls()[-1] == "newProverEnvironment"
                or stmt.getCalls()[-1] == "newProverEnvironmentWithInterpolation"):
            if levels > 0:
                raise Exception("Can't open new prover before closing the last instance")
            active = stmt.variable
            levels = 1
            trace.append(Definition(None, [Call(active), Call("push", [])]))
        elif stmt.getCalls()[-1] == "push":
            levels += 1
            trace.append(stmt)
        elif stmt.getCalls()[-1] == "pop":
            levels -= 1
            trace.append(stmt)
        elif stmt.getCalls() == [active, "close"]:
            trace.extend([Definition(None, [Call(active), Call("pop", [])])] * levels)
            levels = 0
        else:
            trace.append(stmt)
    return trace


def translate(prog: List[Definition]):
    "Convert a JavaSMT trace to a SMTLIB2 script"
    sortMap = {}
    output = ["(set-option :produce-models true)",
              "(set-option :global-declarations true)"]
    for stmt in prog[5:]:
        if stmt.getCalls()[:-1] == ["mgr", "getBitvectorFormulaManager"]:
            if stmt.getCalls()[-1] == "add":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (bvadd {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "and":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (bvand {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "concat":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BitvectorType(sortMap[arg1].width + sortMap[arg2].width)
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (concat {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "distinct":
                args = stmt.value[-1].args
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (distinct {' '.join(args)}))')

            elif stmt.getCalls()[-1] == "divide":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} ({"bvsdiv" if arg3 else "bvudiv"} {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "equal":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (= {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "extend":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = BitvectorType(sortMap[arg1].width + arg2)
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} ((_ {"sign_extend" if arg3 else "zero_extend"} {arg2}) {arg1}))')

            elif stmt.getCalls()[-1] == "extract":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = BitvectorType(arg2 - arg3 + 1)
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} ((_ extract {arg2} {arg3}) {arg1}))')

            elif stmt.getCalls()[-1] == "greaterOrEquals":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (>= {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "greaterThan":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (> {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "lessOrEquals":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (<= {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "lessThan":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (< {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "makeBitvector":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BitvectorType(arg1)
                if arg2 is int:
                    # Create bv constant
                    output.append(
                        f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} {printBitvector(arg1, arg2)})')
                else:
                    # Convert integer formula to bv formula
                    output.append(
                        f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} ((_ int_to_bv {arg1}) {arg2}))')

            elif stmt.getCalls()[-1] == "makeVariable":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]  # We ignore the actual variable name
                sortMap[stmt.variable] = BitvectorType(arg1)
                output.append(f'(declare-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()})')

            elif stmt.getCalls()[-1] == "multiply":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (bvmul {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "negate":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (bvneg {arg1}))')

            elif stmt.getCalls()[-1] == "not":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (bvnot {arg1}))')

            elif stmt.getCalls()[-1] == "or":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (bvor {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "remainder":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} ({"bvsrem" if arg3 else "bvurem"} {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "rotateLeft":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                if not isinstance(arg2, int):
                    raise Exception("rotateLeft is only supported for constant rotations")
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} ((_ rotate_left {arg2}) {arg1}))')

            elif stmt.getCalls()[-1] == "rotateRight":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                if not isinstance(arg2, int):
                    raise Exception("rotateRight is only supported for constant rotations")
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} ((_ rotate_right {arg2}) {arg1}))')

            elif stmt.getCalls()[-1] == "shiftLeft":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (bvshl {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "shiftRight":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} ({"bvashr" if arg3 else "bvlshr"} {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "smod":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (bvsmod {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "subtract":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (bvsub {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "toIntegerFormula":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = IntegerType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} ({"sbv_to_int" if arg2 else "ubv_to_int"} {arg1}))')

            elif stmt.getCalls()[-1] == "xor":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (bvxor {arg1} {arg2}))')

            else:
                raise Exception(f'Unsupported call: {stmt.getCalls()}')

        elif stmt.getCalls()[:-1] == ["mgr", "getBooleanFormulaManager"]:
            if stmt.getCalls()[-1] == "and":
                args = stmt.value[-1].args
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (and {' '.join(args)}))')

            elif stmt.getCalls()[-1] == "equivalence":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (= {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "ifThenElse":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = sortMap[arg2]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (ite {arg1} {arg2} {arg3}))')

            elif stmt.getCalls()[-1] == "implication":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (=> {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "makeFalse":
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} false)')

            elif stmt.getCalls()[-1] == "makeTrue":
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} true)')

            elif stmt.getCalls()[-1] == "makeVariable":
                arg1 = stmt.value[-1].args[0]  # We ignore the actual variable name
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(declare-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()})')

            elif stmt.getCalls()[-1] == "not":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (not {arg1}))')

            elif stmt.getCalls()[-1] == "or":
                args = stmt.value[-1].args
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (or {' '.join(args)}))')

            elif stmt.getCalls()[-1] == "xor":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (xor {arg1} {arg2}))')

            else:
                raise Exception(f'Unsupported call: {stmt.getCalls()}')

        elif stmt.getCalls()[1] == "getIntegerFormulaManager" or stmt.getCalls()[1] == "getRationalFormulaManager":
            if stmt.getCalls()[-1] == "add":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = IntegerType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (+ {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "distinct":
                # FIXME Requires list arguments
                raise Exception("distinct not supported")

            elif stmt.getCalls() == ["mgr", "getIntegerFormulaManager", "divide"]:
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = IntegerType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (div {arg1} {arg2}))')

            elif stmt.getCalls() == ["mgr", "getRationalFormulaManager", "divide"]:
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = RationalType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (/ {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "equal":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (= {arg1} {arg2}))')

            elif stmt.getCalls() == ["mgr", "getIntegerFormulaManager", "floor"]:
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = IntegerType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} {arg1})')

            elif stmt.getCalls() == ["mgr", "getRationalFormulaManager", "floor"]:
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = IntegerType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (to_int {arg1}))')

            elif stmt.getCalls()[-1] == "greaterOrEquals":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (>= {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "greaterThan":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (> {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "lessOrEquals":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (<= {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "lessThan":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (< {arg1} {arg2}))')

            elif stmt.getCalls() == ["mgr", "getIntegerFormulaManager", "makeNumber"]:
                arg1 = stmt.value[-1].args[0]
                if not isinstance(arg1, int):
                    raise Exception("makeNumber is only supported for constant integer arguments")
                sortMap[stmt.variable] = IntegerType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} {arg1})')

            elif stmt.getCalls() == ["mgr", "getRationalFormulaManager", "makeNumber"]:
                arg1 = stmt.value[-1].args[0]
                if not isinstance(arg1, int):
                    # TODO Allow rational values
                    raise Exception("makeNumber is only supported for constant integer arguments")
                sortMap[stmt.variable] = RationalType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} {arg1})')

            elif stmt.getCalls()[-1] == "makeVariable":
                arg1 = stmt.value[-1].args[0]  # We ignore the actual variable name
                sortMap[stmt.variable] = IntegerType()
                output.append(
                    f'(declare-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()})')

            elif stmt.getCalls() == ["mgr", "getIntegerFormulaManager", "modularCongruence"]:
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (= (mod (- {arg1} {arg2}) {arg3}) 0))')

            elif stmt.getCalls() == ["mgr", "getIntegerFormulaManager", "modulo"]:
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = IntegerType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (mod {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "multiply":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = IntegerType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (* {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "negate":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = IntegerType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (- {arg1}))')

            elif stmt.getCalls()[-1] == "subtract":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = IntegerType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (- {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "sum":
                # FIXME Requires list arguments
                raise Exception("sum not supported")

            else:
                raise Exception(f'Unsupported call: {stmt.getCalls()}')

        elif stmt.getCalls()[:-1] == ["mgr", "getArrayFormulaManager"]:
            if stmt.getCalls()[-1] == "equivalence":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (= {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "makeArray":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                if arg1 is Type and arg2 is Type:
                    # Build a const array
                    sortMap[stmt.variable] = ArrayType(arg1, arg2)
                    output.append(
                        f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} ((as const {sortMap[stmt.variable].toSmtlib()}) {arg3}))')
                else:
                    # Declare a new variable
                    sortMap[stmt.variable] = ArrayType(arg2, arg3)
                    output.append(
                        f'(declare-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()})')

            elif stmt.getCalls()[-1] == "select":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1].element
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (select {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "store":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (store {arg1} {arg2} {arg3}))')

            else:
                raise Exception(f'Unsupported call: {stmt.getCalls()}')

        elif stmt.getCalls()[:-1] == ["mgr", "getUFManager"]:
            if stmt.getCalls()[-1] == "callUF":
                arg0 = stmt.value[-1].args[0]
                args = stmt.value[-1].args[1:]
                sortMap[stmt.variable] = sortMap[arg0].value
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} ({arg0} {' '.join(args)}))')

            elif stmt.getCalls()[-1] == "declareUF":
                arg0 = stmt.value[-1].args[0]
                arg1 = stmt.value[-1].args[1]
                args = stmt.value[-1].args[2:]
                sortMap[arg0] = FunctionType(args, arg1)
                output.append(
                    f'(declare-fun {arg0} {sortMap[arg0].toSmtlib()})')

            else:
                raise Exception(f'Unsupported call: {stmt.getCalls()}')

        elif stmt.getCalls()[-1] == "addConstraint":
            arg1 = stmt.value[-1].args[0]
            output.append(f'(assert {arg1})')

        elif stmt.getCalls()[-1] == "asList":
            pass

        elif stmt.getCalls()[-1] == "close":
            pass

        elif stmt.getCalls()[-1] == "getModel":
            output.append(f'(get-model)')

        elif stmt.getCalls()[-1] == "isUnsat":
            output.append(f'(check-sat)')

        elif stmt.getCalls()[-1] == "newProverEnvironment":
            # TODO Apply options at the top of the file
            pass

        elif stmt.getCalls()[-1] == "newProverEnvironmentWithInterpolation":
            # TODO Apply options at the top of the file
            pass

        elif stmt.getCalls()[-1] == "pop":
            output.append(f'(pop 1)')

        elif stmt.getCalls()[-1] == "push":
            output.append(f'(push 1)')

        else:
            raise Exception(f'Unsupported call: {stmt.getCalls()}')

    return '\n'.join(output)


"""
def collect(prog: List[Definition]):
    "List JavaSMT functions that were used in the trace"
    known = set()
    for decl in prog:
        if decl.value[0].fn == "mgr":
            known.add((decl.value[-2].fn, decl.value[-1].fn))
        else:
            known.add(("-", decl.value[-1].fn))
    for p in sorted(known):
        print(p)
"""

if __name__ == '__main__':
    arg = sys.argv
    if not len(sys.argv) == 2:
        print('Expecting a path to a JavaSMT trace as argument')
        exit(-1)

    path = Path(sys.argv[1])
    if not (path.is_file()):
        print(f'Could not find file "{path}"')
        exit(-1)

    # Translate the trace
    print(translate(flattenProvers(program.parse(open(path).read()))))
