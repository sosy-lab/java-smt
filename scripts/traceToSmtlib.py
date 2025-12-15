#!/usr/bin/env python3

# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

import argparse
import math
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
@generate
def litString():
    yield string('"')
    lit = yield regex(r'(\\"|\\\'|\\n|\\\\|[^"])*')
    yield string('"')
    return lit.replace('\\"', '"').replace('\\\'', '\'').replace('\\n', '\n').replace('\\\\', '\\')


def test_string():
    assert litString.parse('"str"') == 'str'
    assert litString.parse('"\\""') == '"'
    assert litString.parse('"\\\\"') == '\\'
    assert litString.parse('"\\\'"') == '\''
    assert litString.parse('"\\n"') == '\n'


class RoundingMode(Enum):
    NEAREST_TIES_TO_EVEN = "FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN"
    NEAREST_TIES_AWAY = "FloatingPointRoundingMode.NEAREST_TIES_AWAY"
    TOWARD_POSITIVE = "FloatingPointRoundingMode.TOWARD_POSITIVE"
    TOWARD_NEGATIVE = "FloatingPointRoundingMode.TOWARD_NEGATIVE"
    TOWARD_ZERO = "FloatingPointRoundingMode.TOWARD_ZERO"

    def toSmtlib(self):
        if self == RoundingMode.NEAREST_TIES_TO_EVEN:
            return "RNE"
        elif self == RoundingMode.NEAREST_TIES_AWAY:
            return "RNA"
        elif self == RoundingMode.TOWARD_POSITIVE:
            return "RTP"
        elif self == RoundingMode.TOWARD_NEGATIVE:
            return "RTN"
        elif self == RoundingMode.TOWARD_ZERO:
            return "RTZ"
        else:
            raise Exception("Unknown rounding mode")


litRoundingMode = from_enum(RoundingMode)


class Sign(Enum):
    POSITIVE = "FloatingPointNumber.Sign.POSITIVE"
    NEGATIVE = "FloatingPointNumber.Sign.NEGATIVE"


litSign = from_enum(Sign)

litType = forward_declaration()

litBoolType = string("FormulaType.BooleanType").map(lambda str: BooleanType())
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
    return FloatType(exponent, 1 + significand)


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
    assert litType.parse("FormulaType.BooleanType") == BooleanType()
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
    BITWUZLA = "SolverContextFactory.Solvers.BITWUZLA"


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


def parseNumber(repr):
    "Parse a String as a number"
    value = None
    try:
        value = int(repr)
    except Exception:
        pass
    if value is not None:
        return value
    try:
        value = Fraction(repr)
    except Exception:
        pass
    if value is not None:
        return value
    try:
        value = float(repr)
    except Exception:
        pass
    if value is not None:
        return value
    else:
        raise Exception(f'Could not parse "{repr}" as a number')


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


@dataclass
class Expr:
    fn: str
    args: Optional[List]

    def toSmtlib(self):
        if self.args == None or self.args == []:
            return self.fn
        else:
            return f'({self.fn} {' '.join([arg.toSmtlib() for arg in self.args])})'


@dataclass
class Def:
    symbol: str
    sort: Type
    value: Optional[Expr]

    def toSmtlib(self):
        if self.value == None:
            if isinstance(self.sort, FunctionType):
                return f'(declare-fun {self.symbol} {self.sort.toSmtlib()})'
            else:
                return f'(declare-const {self.symbol} {self.sort.toSmtlib()})'
        else:
            return f'(define-fun {self.symbol} () {self.sort.toSmtlib()} {self.value.toSmtlib()})'


def const(value):
    return Expr(value, [])


def var(name):
    return Expr(str(name), None)


def app(fn, *args):
    return Expr(fn, [p if isinstance(p, Expr) else var(p) for p in args])


def toIntSmtlib(value):
    "Print integer value as smtlib"
    if isinstance(value, str):
        return toIntSmtlib(parseNumber(value))
    if isinstance(value, float) and not math.isnan(value) and not math.isinf(value):
        return toIntSmtlib(Fraction(value))
    if isinstance(value, int):
        if value < 0:
            return app('-', toIntSmtlib(-value))
        else:
            return const(str(value))
    if isinstance(value, Fraction):
        return app('div', toIntSmtlib(value.numerator), toIntSmtlib(value.numerator))
    else:
        raise Exception(f'Can\'t convert "{value}" to Integer')


def toRealSmtlib(value):
    "Print real value as smtlib"
    if isinstance(value, str):
        return toRealSmtlib(parseNumber(value))
    elif isinstance(value, int):
        return toRealSmtlib(Fraction(value))
    elif isinstance(value, float):
        return toRealSmtlib(Fraction.from_float(value))
    elif isinstance(value, Fraction):
        return app('/', toIntSmtlib(value.numerator), toIntSmtlib(value.denominator))
    else:
        raise Exception(f'Can\'t convert "{value}" to Real')


def toFpSmtlib(rm, fpType, value):
    "Print float value as smtlib"
    if isinstance(value, str):
        return toFpSmtlib(rm, fpType, parseNumber(value))
    elif value == float('-inf'):
        return const(f'(_ -oo {fpType.exponent} {fpType.significand})')
    elif value == float('+inf'):
        return const(f'(_ +oo {fpType.exponent} {fpType.significand})')
    elif isinstance(value, float) and math.isnan(value):
        return const(f'(_ NaN {fpType.exponent} {fpType.significand})')
    else:
        return app(f'(_ to_fp {fpType.exponent} {fpType.significand})', const(rm.toSmtlib()), toRealSmtlib(value))


def translate(prog: List[Definition]):
    "Convert a JavaSMT trace to a SMTLIB2 script"
    # TODO Print error location
    # TODO Use actual variable names in declarations
    sortMap = {}
    nameMap = {}  # Stores UF names for function declarations
    output: List[Def | Expr] = \
        [app('set-logic', const('ALL')),
         app('set-option', const(':interactive-mode'), const('true')),
         app('set-option', const(':produce-models'), const('true')),
         app('set-option', const(':global-declarations'), const('true'))
         ]
    solver = prog[3].value[1].args[3]  # Get solver name from createSolverContext call in the preamble
    for stmt in prog[5:]:
        def matchType(param, arg):
            "Convert argument to match the given type"
            if param == IntegerType() and sortMap[arg] == RationalType():
                return app('to_int', arg)
            elif param == RationalType() and sortMap[arg] == IntegerType():
                return app('to_real', arg)
            else:
                return var(arg)

        if stmt.getCalls()[:-1] == ["mgr", "getBitvectorFormulaManager"]:
            if stmt.getCalls()[-1] == "add":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvadd', arg1, arg2)))

            elif stmt.getCalls()[-1] == "and":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvand', arg1, arg2)))

            elif stmt.getCalls()[-1] == "concat":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BitvectorType(sortMap[arg1].width + sortMap[arg2].width)
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('concat', arg1, arg2)))

            elif stmt.getCalls()[-1] == "distinct":
                args = stmt.value[-1].args[0]
                sortMap[stmt.variable] = BooleanType()
                if len(args) < 2:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], const('true')))
                else:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('distinct', *args)))

            elif stmt.getCalls()[-1] == "divide":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = sortMap[arg1]
                if arg3:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvsdiv', arg1, arg2)))
                else:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvudiv', arg1, arg2)))

            elif stmt.getCalls()[-1] == "equal":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('=', arg1, arg2)))

            elif stmt.getCalls()[-1] == "extend":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = BitvectorType(sortMap[arg1].width + arg2)
                if arg3:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app(f'(_ sign_extend {arg2})', arg1)))
                else:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app(f'(_ zero_extend {arg2})', arg1)))

            elif stmt.getCalls()[-1] == "extract":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = BitvectorType(arg2 - arg3 + 1)
                output.append(Def(stmt.variable, sortMap[stmt.variable], app(f'(_ extract {arg2} {arg3})', arg1)))

            elif stmt.getCalls()[-1] == "greaterOrEquals":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = BooleanType()
                if arg3:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvsge', arg1, arg2)))
                else:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvuge', arg1, arg2)))

            elif stmt.getCalls()[-1] == "greaterThan":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = BooleanType()
                if arg3:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvsgt', arg1, arg2)))
                else:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvugt', arg1, arg2)))

            elif stmt.getCalls()[-1] == "lessOrEquals":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = BooleanType()
                if arg3:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvsle', arg1, arg2)))
                else:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvule', arg1, arg2)))

            elif stmt.getCalls()[-1] == "lessThan":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = BooleanType()
                if arg3:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvslt', arg1, arg2)))
                else:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvult', arg1, arg2)))

            elif stmt.getCalls()[-1] == "makeBitvector":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BitvectorType(arg1)
                if arg2 is int:
                    # Create bv constant
                    output.append(Def(stmt.variable, sortMap[stmt.variable], const(printBitvector(arg1, arg2))))
                else:
                    # Convert integer formula to bv formula
                    operation = "to_bv" if solver == Solvers.MATHSAT5 else "int_to_bv"
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app(f'(_ {operation} {arg1})', arg2)))

            elif stmt.getCalls()[-1] == "makeVariable":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                if '|' in arg2:
                    continue  # Skip illegal names
                sortMap[stmt.variable] = arg1
                output.append(Def(stmt.variable, sortMap[stmt.variable], None))

            elif stmt.getCalls()[-1] == "multiply":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvmul', arg1, arg2)))

            elif stmt.getCalls()[-1] == "negate":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvneg', arg1)))

            elif stmt.getCalls()[-1] == "not":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvnot', arg1)))

            elif stmt.getCalls()[-1] == "or":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvor', arg1, arg2)))

            elif stmt.getCalls()[-1] == "remainder":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = sortMap[arg1]
                if arg3:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvsrem', arg1, arg2)))
                else:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvurem', arg1, arg2)))

            elif stmt.getCalls()[-1] == "rotateLeft":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                if not isinstance(arg2, int):
                    raise Exception("rotateLeft is only supported for constant rotations")
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app(f'(_ rotate_left {arg2})', arg1)))

            elif stmt.getCalls()[-1] == "rotateRight":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                if not isinstance(arg2, int):
                    raise Exception("rotateRight is only supported for constant rotations")
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app(f'(_ rotate_right {arg2})', arg1)))

            elif stmt.getCalls()[-1] == "shiftLeft":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvshl', arg1, arg2)))

            elif stmt.getCalls()[-1] == "shiftRight":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = sortMap[arg1]
                if arg3:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvashr', arg1, arg2)))
                else:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvlshr', arg1, arg2)))

            elif stmt.getCalls()[-1] == "smodulo":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvsmod', arg1, arg2)))

            elif stmt.getCalls()[-1] == "subtract":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvsub', arg1, arg2)))

            elif stmt.getCalls()[-1] == "toIntegerFormula":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = IntegerType()
                if arg2:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('sbv_to_int', arg1)))
                else:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('ubv_to_int', arg1)))

            elif stmt.getCalls()[-1] == "xor":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('bvxor', arg1, arg2)))

            else:
                raise Exception(f'Unsupported call: {stmt.getCalls()}')

        elif stmt.getCalls()[:-1] == ["mgr", "getBooleanFormulaManager"]:
            if stmt.getCalls()[-1] == "and":
                args = stmt.value[-1].args
                sortMap[stmt.variable] = BooleanType()
                if len(args) == 0:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], const('true')))
                elif len(args) == 1:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], var(args[0])))
                else:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('and', *args)))

            elif stmt.getCalls()[-1] == "equivalence":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('=', arg1, arg2)))

            elif stmt.getCalls()[-1] == "ifThenElse":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = sortMap[arg2]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('ite', arg1, arg2, arg3)))

            elif stmt.getCalls()[-1] == "implication":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('=>', arg1, arg2)))

            elif stmt.getCalls()[-1] == "makeFalse":
                sortMap[stmt.variable] = BooleanType()
                output.append(Def(stmt.variable, sortMap[stmt.variable], const('false')))

            elif stmt.getCalls()[-1] == "makeTrue":
                sortMap[stmt.variable] = BooleanType()
                output.append(Def(stmt.variable, sortMap[stmt.variable], const('true')))

            elif stmt.getCalls()[-1] == "makeBoolean":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = BooleanType()
                if arg1:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], const('true')))
                else:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], const('false')))

            elif stmt.getCalls()[-1] == "makeVariable":
                arg1 = stmt.value[-1].args[0]
                if '|' in arg1:
                    continue  # Skip illegal names
                sortMap[stmt.variable] = BooleanType()
                output.append(Def(stmt.variable, sortMap[stmt.variable], None))

            elif stmt.getCalls()[-1] == "not":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('not', arg1)))

            elif stmt.getCalls()[-1] == "or":
                args = stmt.value[-1].args
                sortMap[stmt.variable] = BooleanType()
                if len(args) == 0:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], const('false')))
                elif len(args) == 1:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], var(args[0])))
                else:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('or', *args)))

            elif stmt.getCalls()[-1] == "xor":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('xor', arg1, arg2)))

            else:
                raise Exception(f'Unsupported call: {stmt.getCalls()}')

        elif stmt.getCalls()[1] == "getIntegerFormulaManager" or stmt.getCalls()[1] == "getRationalFormulaManager":
            theoryType = IntegerType() if "Integer" in stmt.getCalls()[1] else RationalType()

            def conv(arg):
                "Convert argument to match the type of the parameter"
                return matchType(theoryType, arg)

            if stmt.getCalls()[-1] == "add":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = theoryType
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('+', conv(arg1), conv(arg2))))

            elif stmt.getCalls()[-1] == "distinct":
                args = stmt.value[-1].args
                sortMap[stmt.variable] = BooleanType()
                if len(args) < 2:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], const('true')))
                else:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('distinct', *[conv(p) for p in args])))

            elif stmt.getCalls()[-1] == "divide":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = theoryType
                if theoryType == IntegerType():
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('div', conv(arg1), conv(arg2))))
                else:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('/', conv(arg1), conv(arg2))))

            elif stmt.getCalls()[-1] == "equal":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('=', conv(arg1), conv(arg2))))

            elif stmt.getCalls()[-1] == "floor":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = IntegerType()
                output.append(Def(stmt.variable, sortMap[stmt.variable], matchType(IntegerType(), arg1)))

            elif stmt.getCalls()[-1] == "greaterOrEquals":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('>=', conv(arg1), conv(arg2))))

            elif stmt.getCalls()[-1] == "greaterThan":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('>', conv(arg1), conv(arg2))))

            elif stmt.getCalls()[-1] == "lessOrEquals":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('<=', conv(arg1), conv(arg2))))

            elif stmt.getCalls()[-1] == "lessThan":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('<', conv(arg1), conv(arg2))))

            elif stmt.getCalls()[-1] == "makeNumber":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = theoryType
                if theoryType == IntegerType():
                    output.append(Def(stmt.variable, sortMap[stmt.variable], toIntSmtlib(arg1)))
                else:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], toRealSmtlib(arg1)))

            elif stmt.getCalls()[-1] == "makeVariable":
                arg1 = stmt.value[-1].args[0]
                if '|' in arg1:
                    continue  # Skip illegal names
                sortMap[stmt.variable] = theoryType
                output.append(Def(stmt.variable, sortMap[stmt.variable], None))

            elif stmt.getCalls() == ["mgr", "getIntegerFormulaManager", "modularCongruence"]:
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = BooleanType()
                output.append(Def(stmt.variable, sortMap[stmt.variable],
                                  app('=', app('mod', app('-', arg1, arg2), toIntSmtlib(arg3)),
                                      toIntSmtlib(0))))

            elif stmt.getCalls() == ["mgr", "getIntegerFormulaManager", "modulo"]:
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = IntegerType()
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('mod', arg1, arg2)))

            elif stmt.getCalls()[-1] == "multiply":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = theoryType
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('*', conv(arg1), conv(arg2))))

            elif stmt.getCalls()[-1] == "negate":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = theoryType
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('-', conv(arg1))))

            elif stmt.getCalls()[-1] == "subtract":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = theoryType
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('-', conv(arg1), conv(arg2))))

            elif stmt.getCalls()[-1] == "sum":
                args = stmt.value[-1].args
                sortMap[stmt.variable] = theoryType
                if len(args) == 0:
                    output.append(Def(stmt.variable, sortMap[stmt.variable],
                                      const('0') if theoryType == IntegerType() else const('0.0')))
                elif len(args) == 1:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], conv(args[0])))
                else:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('+', *[conv(p) for p in args])))

            else:
                raise Exception(f'Unsupported call: {stmt.getCalls()}')

        elif stmt.getCalls()[:-1] == ["mgr", "getFloatingPointFormulaManager"]:
            if stmt.getCalls()[-1] == "abs":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('fp.abs', arg1)))

            elif stmt.getCalls()[-1] == "add":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    Def(stmt.variable, sortMap[stmt.variable], app('fp.add', const(arg3.toSmtlib()), arg1, arg2)))

            elif stmt.getCalls()[-1] == "assignment":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('=', arg1, arg2)))

            elif stmt.getCalls()[-1] == "castTo":
                # Converts from float to bv/int, or convert between different fp precisions
                arg1 = stmt.value[-1].args[0]  # source (fp term)
                arg2 = stmt.value[-1].args[1]  # signed?
                arg3 = stmt.value[-1].args[2]  # target type (any type)
                arg4 = stmt.value[-1].args[3]  # rounding mode
                sortMap[stmt.variable] = arg3
                if isinstance(arg3, FloatType):
                    output.append(Def(stmt.variable, sortMap[stmt.variable],
                                      app(f'(_ to_fp {arg3.exponent} {arg3.significand})', const(arg4.toSmtlib()),
                                          arg1)))
                elif isinstance(arg3, IntegerType):
                    raise Exception("Converting from float to integer is not supported in SMTLIB")
                elif isinstance(arg3, RationalType):
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app('fp.to_real', arg1)))
                elif isinstance(arg3, BitvectorType):
                    if arg2:
                        output.append(Def(stmt.variable, sortMap[stmt.variable],
                                          app(f'(_ fp.to_sbv {arg3.width})', const(arg4.toSmtlib()), arg1)))
                    else:
                        output.append(Def(stmt.variable, sortMap[stmt.variable],
                                          app(f'(_ fp.to_ubv {arg3.width})', const(arg4.toSmtlib()), arg1)))
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
                    output.append(Def(stmt.variable, sortMap[stmt.variable],
                                      app(f'(_ to_fp {arg3.exponent} {arg3.significand})', const(arg4.toSmtlib()),
                                          arg1)))
                elif isinstance(sourceType, IntegerType):
                    raise Exception("Converting from float to integer is not supported in SMTLIB")
                elif isinstance(sourceType, RationalType):
                    output.append(Def(stmt.variable, sortMap[stmt.variable],
                                      app(f'(_ to_fp {arg3.exponent} {arg3.significand})', const(arg4.toSmtlib()),
                                          arg1)))
                elif isinstance(sourceType, BitvectorType):
                    if arg2:
                        output.append(Def(stmt.variable, sortMap[stmt.variable],
                                          app(f'(_ to_fp {arg3.exponent} {arg3.significand})', const(arg4.toSmtlib()),
                                              arg1)))
                    else:
                        output.append(Def(stmt.variable, sortMap[stmt.variable],
                                          app(f'(_ to_fp_unsigned {arg3.exponent} {arg3.significand})',
                                              const(arg4.toSmtlib()),
                                              arg1)))
                else:
                    raise Exception(f"Illegal cast from {sourceType} to float")

            elif stmt.getCalls()[-1] == "divide":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    Def(stmt.variable, sortMap[stmt.variable], app('fp.div', const(arg3.toSmtlib()), arg1, arg2)))

            elif stmt.getCalls()[-1] == "equalWithFPSemantics":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    Def(stmt.variable, sortMap[stmt.variable], app('fp.eq', arg1, arg2)))

            elif stmt.getCalls()[-1] == "fromIeeeBitvector":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = arg2
                output.append(
                    Def(stmt.variable, sortMap[stmt.variable],
                        app(f'(_ to_fp {arg2.exponent} {arg2.significand})', arg1)))

            elif stmt.getCalls()[-1] == "greaterOrEquals":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    Def(stmt.variable, sortMap[stmt.variable], app('fp.geq', arg1, arg2)))

            elif stmt.getCalls()[-1] == "greaterThan":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    Def(stmt.variable, sortMap[stmt.variable], app('fp.gt', arg1, arg2)))

            elif stmt.getCalls()[-1] == "isInfinity":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    Def(stmt.variable, sortMap[stmt.variable], app('fp.isInfinite', arg1)))

            elif stmt.getCalls()[-1] == "isNaN":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    Def(stmt.variable, sortMap[stmt.variable], app('fp.isNaN', arg1)))

            elif stmt.getCalls()[-1] == "isNegative":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    Def(stmt.variable, sortMap[stmt.variable], app('fp.isNegative', arg1)))

            elif stmt.getCalls()[-1] == "isNormal":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    Def(stmt.variable, sortMap[stmt.variable], app('fp.isNormal', arg1)))

            elif stmt.getCalls()[-1] == "isSubnormal":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    Def(stmt.variable, sortMap[stmt.variable], app('fp.isSubnormal', arg1)))

            elif stmt.getCalls()[-1] == "isZero":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = BooleanType()
                output.append(
                    Def(stmt.variable, sortMap[stmt.variable], app('fp.isZero', arg1)))

            elif stmt.getCalls()[-1] == "lessOrEquals":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('fp.leq', arg1, arg2)))

            elif stmt.getCalls()[-1] == "lessThan":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('fp.lt', arg1, arg2)))

            elif stmt.getCalls()[-1] == "makeMinusInfinity":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = arg1
                output.append(
                    Def(stmt.variable, sortMap[stmt.variable], const(f'(_ -oo {arg1.exponent} {arg1.significand})')))

            elif stmt.getCalls()[-1] == "makeNaN":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = arg1
                output.append(
                    Def(stmt.variable, sortMap[stmt.variable], const(f'(_ NaN {arg1.exponent} {arg1.significand})')))

            elif stmt.getCalls()[-1] == "makeNumber":
                args = stmt.value[-1].args
                if (len(args) == 3
                        and (isinstance(args[0], float | int | Fraction | str))
                        and isinstance(args[1], Type)
                        and isinstance(args[2], RoundingMode)):
                    rm = RoundingMode.NEAREST_TIES_TO_EVEN if len(args) == 2 else args[2]
                    sortMap[stmt.variable] = args[1]
                    output.append(Def(stmt.variable, sortMap[stmt.variable], toFpSmtlib(rm, args[1], args[0])))
                elif (len(args) == 4
                      and isinstance(args[0], int)
                      and isinstance(args[1], int)
                      and isinstance(args[2], Sign)
                      and isinstance(args[3], FloatType)):
                    sortMap[stmt.variable] = args[3]
                    output.append(Def(stmt.variable, sortMap[stmt.variable],
                                      app('fp', '#b1' if args[2] == Sign.NEGATIVE else '#b0',
                                          printBitvector(args[3].exponent, args[0]),
                                          printBitvector(args[3].significand - 1, args[1]))))
                else:
                    raise Exception(f'Unsupported call: {stmt.getCalls()} ({type(args[0])} {args})')

            elif stmt.getCalls()[-1] == "makePlusInfinity":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = arg1
                output.append(
                    Def(stmt.variable, sortMap[stmt.variable], const(f'(_ +oo {arg1.exponent} {arg1.significand})')))

            elif stmt.getCalls()[-1] == "makeRoundingMode":
                pass

            elif stmt.getCalls()[-1] == "makeVariable":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                if '|' in arg1:
                    continue  # Skip illegal names
                sortMap[stmt.variable] = arg2
                output.append(Def(stmt.variable, sortMap[stmt.variable], None))

            elif stmt.getCalls()[-1] == "max":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('fp.max', arg1, arg2)))

            elif stmt.getCalls()[-1] == "min":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('fp.min', arg1, arg2)))

            elif stmt.getCalls()[-1] == "multiply":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    Def(stmt.variable, sortMap[stmt.variable], app('fp.mul', const(arg3.toSmtlib()), arg1, arg2)))

            elif stmt.getCalls()[-1] == "negate":
                arg1 = stmt.value[-1].args[0]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('fp.neg', arg1)))

            elif stmt.getCalls()[-1] == "remainder":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('fp.rem', arg1, arg2)))

            elif stmt.getCalls()[-1] == "round":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    Def(stmt.variable, sortMap[stmt.variable], app('fp.roundToIntegral', const(arg2.toSmtlib()), arg1)))

            elif stmt.getCalls()[-1] == "sqrt":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('fp.sqrt', const(arg2.toSmtlib()), arg1)))

            elif stmt.getCalls()[-1] == "subtract":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(
                    Def(stmt.variable, sortMap[stmt.variable], app('fp.sub', const(arg3.toSmtlib()), arg1, arg2)))

            elif stmt.getCalls()[-1] == "toIeeeBitvector":
                raise Exception("Extracting the bits of a floating-point value is not supported in SMTLIB")

            else:
                raise Exception(f'Unsupported call: {stmt.getCalls()}')

        elif stmt.getCalls()[:-1] == ["mgr", "getArrayFormulaManager"]:
            if stmt.getCalls()[-1] == "equivalence":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = BooleanType()
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('=', arg1, arg2)))

            elif stmt.getCalls()[-1] == "makeArray":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                if isinstance(arg1, Type) and isinstance(arg2, Type):
                    # Build a const array
                    sortMap[stmt.variable] = ArrayType(arg1, arg2)
                    output.append(Def(stmt.variable, sortMap[stmt.variable],
                                      app(f'(as const {sortMap[stmt.variable].toSmtlib()})', arg3)))
                else:
                    # Declare a new variable
                    sortMap[stmt.variable] = ArrayType(arg2, arg3)
                    output.append(Def(stmt.variable, sortMap[stmt.variable], None))

            elif stmt.getCalls()[-1] == "select":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                sortMap[stmt.variable] = sortMap[arg1].element
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('select', arg1, arg2)))

            elif stmt.getCalls()[-1] == "store":
                arg1 = stmt.value[-1].args[0]
                arg2 = stmt.value[-1].args[1]
                arg3 = stmt.value[-1].args[2]
                sortMap[stmt.variable] = sortMap[arg1]
                output.append(Def(stmt.variable, sortMap[stmt.variable], app('store', arg1, arg2, arg3)))

            else:
                raise Exception(f'Unsupported call: {stmt.getCalls()}')

        elif stmt.getCalls()[:-1] == ["mgr", "getQuantifiedFormulaManager"]:
            # TODO
            raise Exception(f'Quantifiers are not supported yet')

        elif stmt.getCalls()[:-1] == ["mgr", "getStringFormulaManager"]:
            # TODO
            raise Exception(f'Strings are not supported yet')

        elif stmt.getCalls()[:-1] == ["mgr", "getEnumerationFormulaManager"]:
            # TODO
            raise Exception(f'Enumerations are not supported yet')

        elif stmt.getCalls()[:-1] == ["mgr", "getSLFormulaManager"]:
            # TODO
            raise Exception(f'Separation logic is not supported yet')

        elif stmt.getCalls()[:-1] == ["mgr", "getUFManager"]:
            if stmt.getCalls()[-1] == "callUF":
                arg0 = stmt.value[-1].args[0]
                args = stmt.value[-1].args[1]
                name = nameMap[arg0]
                values = [matchType(param, arg) for param, arg in zip(sortMap[arg0].arguments, args)]
                sortMap[stmt.variable] = sortMap[arg0].value
                if args == []:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], None))
                else:
                    output.append(Def(stmt.variable, sortMap[stmt.variable], app(name, *values)))

            elif stmt.getCalls()[-1] == "declareUF":
                arg0 = stmt.value[-1].args[0]
                arg1 = stmt.value[-1].args[1]
                args = stmt.value[-1].args[2]
                if '|' in arg0:
                    continue  # Skip illegal names
                sortMap[stmt.variable] = FunctionType(args, arg1)
                nameMap[stmt.variable] = f'|{arg0}|'
                if args != []:
                    output.append(Def(nameMap[stmt.variable], sortMap[stmt.variable], None))

            else:
                raise Exception(f'Unsupported call: {stmt.getCalls()}')

        elif stmt.getCalls()[-1] == "addConstraint":
            arg1 = stmt.value[-1].args[0]
            output.append(app('assert', arg1))

        elif stmt.getCalls()[-1] == "asList":
            pass

        elif stmt.getCalls()[-1] == "close":
            pass

        elif stmt.getCalls()[-1] == "evaluate":
            arg1 = stmt.value[-1].args[0]
            output.append(app('get-value', app('', arg1)))

        elif stmt.getCalls()[-1] == "getModel":
            output.append(const('(get-model)'))

        elif stmt.getCalls()[-1] == "isUnsat":
            output.append(const('(check-sat)'))

        elif stmt.getCalls() == ["mgr", "makeVariable"]:
            arg1 = stmt.value[-1].args[0]
            arg2 = stmt.value[-1].args[1]
            if '|' in arg2:
                continue  # Skip illegal names
            sortMap[stmt.variable] = arg1
            output.append(Def(stmt.variable, sortMap[stmt.variable], None))

        elif stmt.getCalls()[-1] == "newProverEnvironment":
            # TODO Apply options at the top of the file
            pass

        elif stmt.getCalls()[-1] == "newProverEnvironmentWithInterpolation":
            # TODO Apply options at the top of the file
            pass

        elif stmt.getCalls()[-1] == "pop":
            output.append(app('pop', const('1')))

        elif stmt.getCalls()[-1] == "push":
            output.append(app('push', const('1')))

        else:
            raise Exception(f'Unsupported call: {stmt.getCalls()}')

    return output


def printSmtlib(program):
    "Convert intermediate representation to String"
    return '\n'.join([line.toSmtlib() for line in program]) + '\n'


if __name__ == '__main__':
    options = argparse.ArgumentParser(description='Convert JavaSMT traces to SMTLIB files')

    options.add_argument('file', type=Path, help='Input file')
    options.add_argument('--save', action='store_true',
                         help='Save the output in a *.smt2 file. The path to the file is the same as for the input, but with a different extension')

    args = options.parse_args()

    if not args.file.is_file():
        print(f'Could not find input file "{args.file}"')
        exit(-1)

    # Translate the trace
    try:
        output = printSmtlib(translate(flattenProvers(program.parse("\n" + open(args.file).read()))))
    except Exception as exception:
        print(f'In {args.file}: {exception}')
        exit(-1)

    out = open(args.file.with_suffix('.smt2'), 'w') if args.save else sys.stdout
    out.write(output)
    out.close()
