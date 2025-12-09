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
from fractions import Fraction
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

argument = forward_declaration()

# Boolean constants
litBool = string("true").map(lambda str: True) | string("false").map(lambda str: False)


def test_bool():
    assert litBool.parse('true') == True
    assert litBool.parse('false') == False


litNumeral = regex(r'0|-?[1-9][0-9]*').map(int)


@generate
def litDecimal():
    sign = yield string('-').optional()
    integer = yield regex(r'0|[1-9][0-9]*')
    yield string(".")
    fraction = yield regex(r'[0-9]*')
    shift = len(fraction)
    num = int(integer) * 10 ** shift + int(fraction)
    den = 10 ** shift
    return Fraction(num if sign is None else -num, den)


@generate
def litFpConstant():
    sign = yield string('-').optional("")
    integerPart = yield regex(r'[0-9]+')
    yield string('.')
    fractionPart = yield regex(r'[0-9]+')
    exponentPart = "0"
    hasExponent = yield string('E').optional()
    if hasExponent is not None:
        exponentPart = yield regex(r'-?[0-9]+')
    return float(sign + integerPart + '.' + fractionPart + "e" + exponentPart)


# Integer constants
litInt = litNumeral << string("L").optional()

# Double constants
litFloat = string("Double.NaN").map(lambda str: float('nan')) | \
           string("Double.POSITIVE_INFINITY").map(lambda str: float('inf')) | \
           string("Double.NEGATIVE_INFINITY").map(lambda str: float('-inf')) | \
           litFpConstant


# BigInteger constants
@generate
def litBigInteger():
    yield string('new') >> whitespace >> string('BigInteger(') >> whitespace.optional()
    yield string('"')
    integer = yield litNumeral
    yield string('"')
    yield whitespace.optional() << string(')')
    return integer


# BigDecimal constants
@generate
def litBigDecimal():
    yield string('new') >> whitespace >> (string('BigDecimal(')) >> whitespace.optional()
    yield string('"')
    number = yield (litDecimal | litNumeral)
    yield string('"')
    yield whitespace.optional() << string(')')
    return number


# Rational constants
@generate
def litRational():
    yield string('Rational.of("')
    num = yield regex(r'-?[0-9]+').map(int)
    isFraction = yield string("/").optional()
    den = 1
    if isFraction is not None:
        den = yield regex(r'[0-9]+').map(int)
    yield string('")')
    return Fraction(num, den)


litNumber = litBigInteger | litBigDecimal | litRational | litFloat | litInt


def test_number():
    assert litNumber.parse('123') == 123
    assert litNumber.parse('-123') == -123
    assert litNumber.parse('123L') == 123
    assert litNumber.parse('0.0') == 0.0
    assert litNumber.parse('1.23') == 1.23
    assert litNumber.parse('-1.23') == -1.23
    assert litNumber.parse('12.3E1') == 123.0
    assert litNumber.parse('12.3E-1') == 1.23
    assert litNumber.parse('Double.NEGATIVE_INFINITY') == float('-inf')
    assert litNumber.parse('new BigInteger("123")') == 123
    assert litNumber.parse('new BigDecimal("123")') == Fraction(123)
    assert litNumber.parse('new BigDecimal("123.4")') == Fraction(1234, 10)
    assert litNumber.parse('new BigDecimal("0.0625")') == Fraction(625, 10000)
    assert litNumber.parse('Rational.of("4")') == Fraction(4)
    assert litNumber.parse('Rational.of("1/4")') == Fraction(1, 4)


# String constants
litString = regex(r'"(\\"|[^"])*"').map(lambda str: str.replace(r'\"', '"').replace(r'\n', '\n'))


def test_string():
    assert litString.parse('"str"') == "str"


class RoundingMode(Enum):
    NEAREST_TIES_TO_EVEN = "FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN"
    NEAREST_TIES_AWAY = "FloatingPointRoundingMode.NEAREST_TIES_AWAY"
    TOWARD_POSITIVE = "FloatingPointRoundingMode.TOWARD_POSITIVE"
    TOWARD_NEGATIVE = "FloatingPointRoundingMode.TOWARD_NEGATIVE"
    TOWARD_ZERO = "FloatingPointRoundingMode.TOWARD_ZERO"


litRoundingMode = from_enum(RoundingMode)


class Sign(Enum):
    POSITIVE = "FloatingPointNumber.Sign.POSITIVE"
    NEGATIVE = "FloatingPointNumber.Sign.NEGATIVE"


litSign = from_enum(Sign)

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
    yield string("FormulaType.getFloatingPointType(") >> whitespace.optional()
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


class Quantifier(Enum):
    FORALL = "QuantifiedFormulaManager.Quantifier.FORALL"
    EXISTS = "QuantifiedFormulaManager.Quantifier.EXISTS"


litQuantifier = from_enum(Quantifier)


@generate
def litList():
    yield (string("List.of(") | string("ImmutableList.of(") | string("Set.of("))
    yield whitespace.optional()
    arg0 = yield argument.optional().map(lambda p: [p] if p is not None else [])
    args = []
    if (arg0 is not []):
        args = yield (whitespace.optional() >> string(",") >> whitespace.optional() >> argument).many()
    yield whitespace.optional()
    yield string(")")
    return arg0 + args


def test_list():
    assert litList.parse("List.of(1, 2, var)") == [1, 2, "var"]
    assert litList.parse("ImmutableList.of()") == []
    assert litList.parse("List.of(ImmutableList.of(1,2), ImmutableList.of(3,7))") == [[1, 2], [3, 7]]
    assert litList.parse("Set.of(1,2)") == [1, 2]


variable = regex(r"[A-Za-z][A-Za-z0-9]*")


def test_variable():
    assert variable.parse("var1") == "var1"
    assert variable.parse("mgr") == "mgr"


argument.become(alt(
    litBool,
    litNumber,
    litRoundingMode,
    litSign,
    litString,
    litType,
    litSolvers,
    litProverOptions,
    litQuantifier,
    litList,
    variable))


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
            == "(Array Int (Array (_ BitVec 32) (_ FloatingPoint 8 24)))")


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
    nameMap = {}  # Stores UF names for function declarations
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
                args = stmt.value[-1].args[0]
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

            elif stmt.getCalls()[-1] == "smodulo":
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

            elif stmt.getCalls()[-1] == "makeBoolean":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(declare-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} {'true' if arg1 else 'false'})')

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
                args = stmt.value[-1].args[0]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (distinct {' '.join(args)}))')

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
                sortMap[stmt.variable] = IntegerType()
                if isinstance(arg1, int):
                    output.append(
                        f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} {arg1 if arg1 >= 0 else f'(- {abs(arg1)})'})')
                elif isinstance(arg1, Fraction):
                    output.append(
                        f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (div {arg1.numerator} {arg1.denominator}))')
                elif isinstance(arg1, float):
                    # FIXME We need to use euclidean division here. Converting with int() will (probably?) truncate
                    output.append(
                        f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} {int(arg1)})')
                else:
                    raise Exception("makeNumber is only supported for constant integer arguments")

            elif stmt.getCalls() == ["mgr", "getRationalFormulaManager", "makeNumber"]:
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = RationalType()
                if isinstance(arg1, int):
                    output.append(
                        f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} {arg1})')
                elif isinstance(arg1, Fraction):
                    output.append(
                        f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (/ {arg1.numerator} {arg1.denominator}))')
                elif isinstance(arg1, float):
                    output.append(
                        f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} {arg1})')
                else:
                    raise Exception("makeNumber is only supported for constant integer arguments")

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
                args = stmt.value[-1].args[0]
                sortMap[stmt.variable] = IntegerType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (+ {' '.join(args)}))')

            else:
                raise Exception(f'Unsupported call: {stmt.getCalls()}')

        elif stmt.getCalls()[:-1] == ["mgr", "getFloatingPointFormulaManager"]:
            if stmt.getCalls()[-1] == "abs":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (fp.abs {arg1}))')

            elif stmt.getCalls()[-1] == "add":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (fp.add {arg3} {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "assignment":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (= {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "castTo":
                # Converts from float to bv/int, or convert between different fp precisions
                arg1 = stmt.value[-1].args[0]  # source (fp term)
                arg2 = stmt.value[-1].args[1]  # signed?
                arg3 = stmt.value[-1].args[2]  # target type (any type)
                arg4 = stmt.value[-1].args[3]  # rounding mode
                sortMap[stmt.variable] = arg3
                if isinstance(arg3, FloatType):
                    output.append(
                        f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} ((_ to_fp {arg3.exponent} {arg3.significand}) {arg4} {arg1})')
                elif isinstance(arg3, IntegerType):
                    raise Exception("Converting from float to integer is not supported in SMTLIB")
                elif isinstance(arg3, RationalType):
                    output.append(
                        f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (fp.to_real {arg1})')
                elif isinstance(arg3, BitvectorType):
                    output.append(
                        f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} ((_ {'fp.to_sbv' if arg2 else 'fp.to_ubv'}  {arg3.width}) {arg4} {arg1})')
                else:
                    raise Exception(f"Illegal cast from float to {arg3}")

            elif stmt.getCalls()[-1] == "castFrom":
                # Converts from bv/int to float, or convert between different fp precisions
                arg1 = stmt.value[-1].args[0]  # source (any term)
                arg2 = stmt.value[-1].args[1]  # signed?
                arg3 = stmt.value[-1].args[2]  # target type (fp type)
                arg4 = stmt.value[-1].args[3]  # rounding mode
                sortMap[stmt.variable] = arg3
                sourceType = sortMap[arg1]
                if isinstance(sourceType, FloatType):
                    output.append(
                        f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} ((_ to_fp {arg3.exponent} {arg3.significand}) {arg4} {arg1})')
                elif isinstance(sourceType, IntegerType):
                    raise Exception("Converting from float to integer is not supported in SMTLIB")
                elif isinstance(sourceType, RationalType):
                    output.append(
                        f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} ((_ to_fp {arg3.exponent} {arg3.significand}) {arg1})')
                elif isinstance(sourceType, BitvectorType):
                    output.append(
                        f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} ((_ {'to_fp' if arg2 else 'to_fp_unsigned'}  {arg3.exponent}) {arg3.significand}) {arg3} {arg1})')
                else:
                    raise Exception(f"Illegal cast from {sourceType} to float")

            elif stmt.getCalls()[-1] == "divide":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (fp.div {arg3} {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "equalWithFPSemantics":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (fp.eq {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "fromIeeeBitvector":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} ((_ to_fp {arg2.exponent} {arg2.significand}) {arg1}))')

            elif stmt.getCalls()[-1] == "greaterOrEquals":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (fp.geq {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "greaterThan":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (fp.gt {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "lessOrEquals":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (fp.leq {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "lessThan":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (fp.lt {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "makeMinusInfinity":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = FloatType(arg1.exponent, arg1.significand)
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (_ -oo {arg1.exponent} {arg1.significand}))')

            elif stmt.getCalls()[-1] == "makeNaN":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = FloatType(arg1.exponent, arg1.significand)
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (_ NaN {arg1.exponent} {arg1.significand}))')

            elif stmt.getCalls()[-1] == "makeNumber":
                if len(stmt.value[-1].args) < 4:
                    raise Exception(f'Expected 4 arguments to fp.makeNumber, got {len(stmt.value)}')
                arg1 = stmt.value[-1].args[0]  # exponent
                arg2 = stmt.value[-1].args[1]  # significand
                arg3 = stmt.value[-1].args[2]  # sign
                arg4 = stmt.value[-1].args[3]  # type
                if not (isinstance(arg1, int) and
                        isinstance(arg2, int) and
                        isinstance(arg3, Sign) and
                        isinstance(arg4, FloatType)):
                    # TODO Support more value constructors
                    raise Exception(
                        "We currently only support fp.makeNumber when sign, exponent and mantissa are given explicitly")
                sortMap[stmt.variable] = arg4
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (fp {'#1' if arg3 == Sign.NEGATIVE else '#0'} {printBitvector(arg4.exponent, arg1)} {printBitvector(arg4.significand, arg2)}))')

            elif stmt.getCalls()[-1] == "makePlusInfinity":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = FloatType(arg1.exponent, arg1.significand)
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (_ +oo {arg1.exponent} {arg1.significand}))')

            elif stmt.getCalls()[-1] == "makeVariable":
                arg1 = stmt.value[-1].args[0]  # We ignore the actual variable name
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = arg2
                output.append(
                    f'(declare-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()})')

            elif stmt.getCalls()[-1] == "max":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (fp.max {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "min":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (fp.min {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "multiply":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (fp.mul {arg3} {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "negate":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (fp.neg {arg1}))')

            elif stmt.getCalls()[-1] == "remainder":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (fp.rem {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "round":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (fp.roundToIntegral {arg2} {arg1}))')

            elif stmt.getCalls()[-1] == "sqrt":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (fp.sqrt {arg2} {arg1}))')

            elif stmt.getCalls()[-1] == "subtract":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} (fp.sub {arg3} {arg1} {arg2}))')

            elif stmt.getCalls()[-1] == "toIeeBitvector":
                raise Exception("Recasting from float to bitvector is not supported in SMTLIB")

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
                if isinstance(arg1, Type) and isinstance(arg2, Type):
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
                name = nameMap[arg0]
                sortMap[stmt.variable] = sortMap[arg0].value
                output.append(
                    f'(define-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()} ({name} {' '.join(args)}))')

            elif stmt.getCalls()[-1] == "declareUF":
                arg0 = stmt.value[-1].args[0]
                arg1 = stmt.value[-1].args[1]
                args = stmt.value[-1].args[2:]
                sortMap[stmt.variable] = FunctionType(args, arg1)
                nameMap[stmt.variable] = arg0
                output.append(
                    f'(declare-fun {arg0} {sortMap[stmt.variable].toSmtlib()})')

            else:
                raise Exception(f'Unsupported call: {stmt.getCalls()}')

        elif stmt.getCalls()[-1] == "addConstraint":
            arg1 = stmt.value[-1].args[0]
            output.append(f'(assert {arg1})')

        elif stmt.getCalls()[-1] == "asList":
            pass

        elif stmt.getCalls()[-1] == "close":
            pass

        elif stmt.getCalls()[-1] == "evaluate":
            arg1 = stmt.value[-1].args[0]
            output.append(f'(get-values ({arg1}))')

        elif stmt.getCalls()[-1] == "getModel":
            output.append(f'(get-model)')

        elif stmt.getCalls()[-1] == "isUnsat":
            output.append(f'(check-sat)')

        elif stmt.getCalls() == ["mgr", "makeVariable"]:
            arg1 = stmt.value[-1].args[0]
            arg2 = stmt.value[-1].args[1]  # We ignore the actual variable name
            sortMap[stmt.variable] = arg1
            output.append(
                f'(declare-const {stmt.variable} {sortMap[stmt.variable].toSmtlib()})')

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
