// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

/**
 * Types of function declarations.
 *
 * @see FunctionDeclaration
 */
public enum FunctionDeclarationKind {
  AND,
  NOT,
  OR,

  /** If and only if. */
  IFF,

  /** If-then-else operator. */
  ITE,

  /** Exclusive OR over two formulas. */
  XOR,

  /** Implication between two boolean formulas. */
  IMPLIES,

  /** Distinct operator for a set of numeric formulas. */
  DISTINCT,

  /** Store and select on arrays, and constant initialization. */
  STORE,
  SELECT,
  CONST,

  // Simple arithmetic,
  // they work across integers and rationals.

  /** Unary minus. */
  UMINUS,

  /** Subtraction over integers and rationals. */
  SUB,

  /** Addition over integers and rationals. */
  ADD,

  /** Division over rationals and integer division over integers. */
  DIV,

  /** Multiplication over integers and rationals. */
  MUL,

  /** Modulo operator over integers. */
  MODULO,

  /** Uninterpreted function. */
  UF,

  /** User-defined variable. */
  VAR,

  /** Less-than over integers and rationals. */
  LT,

  /** Less-than-or-equal over integers and rationals. */
  LTE,

  /** Greater-than over integers and rationals. */
  GT,

  /** Greater-than-or-equal over integers and rationals. */
  GTE,

  /** Equality over integers and rationals. Binary equality is modelled with {@code IFF}. */
  EQ,

  /** Unary comparison to zero. */
  EQ_ZERO,

  /** Unary comparison with zero. */
  GTE_ZERO,

  /** Floor operation, converts from rationals to integers, also known as {@code to_int}. */
  FLOOR,

  /** Identity operation, converts from integers to rationals, also known as {@code to_real}. */
  TO_REAL,

  /** Convert from integer to bitvector. */
  INT_TO_BV,

  // Simple bitvector operations

  /** Extraction over bitvectors. */
  BV_EXTRACT,

  /** Concatenation over bitvectors. */
  BV_CONCAT,

  /** Extend bitvectors according to their sign. */
  BV_SIGN_EXTENSION,

  /** Extend bitvectors with zeros. */
  BV_ZERO_EXTENSION,

  /** Bitwise negation of a bitvector. */
  BV_NOT,

  /** Negation of a bitvector. */
  BV_NEG,

  /** Bitwise OR over bitvectors. */
  BV_OR,

  /** Bitwise AND over bitvectors. */
  BV_AND,

  /** Bitwise XOR over bitvectors. */
  BV_XOR,

  /** Subtraction over bitvectors. */
  BV_SUB,

  /** Addition over bitvectors. */
  BV_ADD,

  /** Signed division over bitvectors. */
  BV_SDIV,

  /** Unsigned division over bitvectors. */
  BV_UDIV,

  /** Signed remainder over bitvectors. */
  BV_SREM,

  /** Unsigned remainder over bitvectors. */
  BV_UREM,

  /** Signed modulo over bitvectors. */
  BV_SMOD,

  /** Multiplication over bitvectors. */
  BV_MUL,

  /** Signed less-than over bitvectors. */
  BV_ULT,

  /** Unsigned less-than over bitvectors. */
  BV_SLT,

  /** Unsigned less-than-or-equal over bitvectors. */
  BV_ULE,

  /** Signed greater-than-or-equal over bitvectors. */
  BV_SLE,

  /** Signed greater-than over bitvectors. */
  BV_UGT,

  /** Unsigned greater-than over bitvectors. */
  BV_SGT,

  /** Unsigned greater-than-or-equal over bitvectors. */
  BV_UGE,

  /** Signed greater-than-or-equal over bitvectors. */
  BV_SGE,

  /** Equality over bitvectors. Binary equality is modeled with {@code IFF}. */
  BV_EQ,

  /** Logical left-shift over bitvectors (fill from right with zeroes). */
  BV_SHL,

  /** Logical right-shift over bitvectors (fill from left with zeroes). */
  BV_LSHR,

  /** Arithmetic right-shift over bitvectors (fill from left with value of first bit). */
  BV_ASHR,

  /** Performs a circular left rotation on the bitvector. */
  BV_ROTATE_LEFT,

  /** Performs a circular right rotation on the bitvector. */
  BV_ROTATE_RIGHT,

  /**
   * Performs a circular left rotation on the bitvector by a specified number of positions,
   * determined by an integer value.
   */
  BV_ROTATE_LEFT_BY_INT,

  /**
   * Performs a circular right rotation on the bitvector by a specified number of positions,
   * determined by an integer value.
   */
  BV_ROTATE_RIGHT_BY_INT,

  /** Cast an unsigned bitvector to a floating-point number. */
  BV_UCASTTO_FP,

  /** Cast a signed bitvector to a floating-point number. */
  BV_SCASTTO_FP,

  /** Cast an unsigned bitvector to an integer number. */
  UBV_TO_INT,

  /** Cast a signed bitvector to an integer number. */
  SBV_TO_INT,

  // Simple floating point operations

  /** Negation of a floating point. */
  FP_NEG,

  /** Absolute value of a floating point. */
  FP_ABS,

  /** Maximum of two floating points. */
  FP_MAX,

  /** Minimum of two floating points. */
  FP_MIN,

  /** Square root of a floating point. */
  FP_SQRT,

  /** Subtraction over floating points. */
  FP_SUB,

  /** Addition over floating points. */
  FP_ADD,

  /** Division over floating points. */
  FP_DIV,

  /** Remainder of the floating point division. */
  FP_REM,

  /** Multiplication over floating points. */
  FP_MUL,

  /** Less-than over floating points. */
  FP_LT,

  /** Less-than-or-equal over floating points. */
  FP_LE,

  /** Greater-than-or-equal over floating points. */
  FP_GE,

  /** Greater-than over floating points. */
  FP_GT,

  /** Equal over floating points. */
  FP_EQ,

  /** Rounding over floating points. */
  FP_ROUND_TO_INTEGRAL,

  /** Further FP queries. */
  FP_IS_NAN,
  FP_IS_INF,
  FP_IS_ZERO,
  FP_IS_NEGATIVE,
  FP_IS_SUBNORMAL,
  FP_IS_NORMAL,

  FP_CASTTO_FP,
  FP_CASTTO_SBV,
  FP_CASTTO_UBV,
  FP_AS_IEEEBV,
  FP_FROM_IEEEBV,

  // String and Regex theory

  STR_CONCAT,
  STR_PREFIX,
  STR_SUFFIX,
  STR_CONTAINS,
  STR_SUBSTRING,
  STR_REPLACE,
  STR_REPLACE_ALL,
  STR_CHAR_AT,
  STR_LENGTH,
  STR_INDEX_OF,
  STR_TO_RE,
  STR_IN_RE,
  STR_TO_INT,
  INT_TO_STR,
  STR_FROM_CODE,
  STR_TO_CODE,
  STR_LT,
  STR_LE,

  RE_NONE,
  RE_PLUS,
  RE_STAR,
  RE_OPTIONAL,
  RE_CONCAT,
  RE_UNION,
  RE_RANGE,
  RE_INTERSECT,
  RE_COMPLEMENT,
  RE_DIFFERENCE,

  // Separation logic
  SEP_EMP,
  SEP_NIL,
  SEP_PTO,
  SEP_STAR,
  SEP_WAND,

  // default case

  /**
   * Solvers support a lot of different built-in theories. We enforce standardization only across a
   * small subset.
   */
  OTHER;

  public static int getArity(FunctionDeclarationKind pKind) {
    return switch (pKind) {
      case AND,
          OR,
          IFF,
          XOR,
          IMPLIES,
          DISTINCT,
          SUB,
          ADD,
          DIV,
          MUL,
          LT,
          LTE,
          GT,
          GTE,
          EQ,
          BV_CONCAT,
          BV_OR,
          BV_AND,
          BV_XOR,
          BV_SUB,
          BV_ADD,
          BV_MUL,
          STR_CONCAT,
          STR_LT,
          STR_LE,
          RE_CONCAT,
          RE_DIFFERENCE,
          RE_UNION,
          RE_INTERSECT ->
          -1;
      case RE_NONE, SEP_NIL -> 0;
      case INT_TO_BV,
          NOT,
          UMINUS,
          EQ_ZERO,
          GTE_ZERO,
          FLOOR,
          TO_REAL,
          CONST,
          BV_EXTRACT,
          BV_SIGN_EXTENSION,
          BV_ZERO_EXTENSION,
          BV_NOT,
          BV_NEG,
          BV_ROTATE_LEFT_BY_INT,
          BV_ROTATE_RIGHT_BY_INT,
          UBV_TO_INT,
          SBV_TO_INT,
          FP_NEG,
          FP_ABS,
          FP_IS_NAN,
          FP_IS_INF,
          FP_IS_ZERO,
          FP_IS_NEGATIVE,
          FP_IS_SUBNORMAL,
          FP_IS_NORMAL,
          FP_AS_IEEEBV,
          FP_FROM_IEEEBV,
          RE_PLUS,
          RE_STAR,
          INT_TO_STR,
          STR_FROM_CODE,
          STR_TO_CODE,
          STR_LENGTH,
          STR_TO_INT,
          STR_TO_RE,
          RE_COMPLEMENT,
          RE_OPTIONAL ->
          1;
      case SELECT,
          MODULO,
          BV_SDIV,
          BV_UDIV,
          BV_SREM,
          BV_UREM,
          BV_SMOD,
          BV_ULT,
          BV_SLT,
          BV_ULE,
          BV_SLE,
          BV_UGT,
          BV_SGT,
          BV_UGE,
          BV_SGE,
          BV_SHL,
          BV_LSHR,
          BV_ASHR,
          BV_ROTATE_LEFT,
          BV_ROTATE_RIGHT,
          BV_UCASTTO_FP,
          BV_SCASTTO_FP,
          FP_MAX,
          FP_MIN,
          FP_SQRT,
          FP_REM,
          FP_LT,
          FP_LE,
          FP_GE,
          FP_GT,
          FP_EQ,
          FP_ROUND_TO_INTEGRAL,
          FP_CASTTO_FP,
          FP_CASTTO_SBV,
          FP_CASTTO_UBV,
          STR_CHAR_AT,
          STR_CONTAINS,
          STR_IN_RE,
          STR_PREFIX,
          STR_SUFFIX,
          RE_RANGE,
          SEP_PTO,
          SEP_EMP,
          SEP_STAR,
          SEP_WAND ->
          2;
      case ITE,
          STORE,
          FP_SUB,
          FP_ADD,
          FP_DIV,
          FP_MUL,
          STR_INDEX_OF,
          STR_REPLACE,
          STR_REPLACE_ALL,
          STR_SUBSTRING ->
          3;
      default ->
          throw new IllegalArgumentException(String.format("Unsupported kind: \"%s\"", pKind));
    };
  }

  public static int getNumIndices(FunctionDeclarationKind pKind) {
    // TODO Add missing kinds
    return switch (pKind) {
      case BV_ROTATE_LEFT_BY_INT, BV_ROTATE_RIGHT_BY_INT, BV_SIGN_EXTENSION, BV_ZERO_EXTENSION -> 1;
      case BV_EXTRACT -> 2;
      default -> 0;
    };
  }
}
