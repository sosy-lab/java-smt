/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

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

  /** Exclusive OR over two variables. */
  XOR,
  IMPLIES,
  DISTINCT,

  /** Store and select on arrays */
  STORE,
  SELECT,

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

  // Simple bitvector operations

  /** Extraction over bitvectors. */
  BV_EXTRACT,

  /** Concatenation over bitvectors. */
  BV_CONCAT,

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

  /** Multiplication over bitvectors. */
  BV_MUL,

  /** Modulo operator over bitvectors. */
  BV_MODULO,

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

  /**
   * Solvers support a lot of different built-in theories. We enforce standardization only across a
   * small subset.
   */
  OTHER;
}
