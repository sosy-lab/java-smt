package org.sosy_lab.solver.api;

import org.sosy_lab.solver.basicimpl.FunctionDeclarationImpl;

/**
 * Types of function declarations.
 *
 * @see FunctionDeclarationImpl
 */
public enum FunctionDeclarationKind {
  AND,
  NOT,
  OR,

  /**
   * If and only if.
   */
  IFF,

  /**
   * If-then-else operator.
   */
  ITE,

  /**
   * Exclusive OR over two variables.
   */
  XOR,
  IMPLIES,
  DISTINCT,

  /**
   * Store and select on arrays
   */
  STORE,
  SELECT,

  // Simple arithmetic,
  // they work across integers and rationals.
  /**
   * Subtraction over integers and rationals.
   */
  SUB,

  /**
   * Addition over integers and rationals.
   */
  ADD,

  /**
   * Division over rationals and integer division over integers.
   */
  DIV,

  /**
   * Multiplication over integers and rationals.
   */
  MUL,

  /**
   * Modulo operator over integers.
   */
  MODULO,

  /**
   * Uninterpreted function.
   */
  UF,

  /**
   * User-defined variable.
   */
  VAR,

  /**
   * Less-than over integers and rationals.
   */
  LT,

  /**
   * Less-than-or-equal over integers and rationals.
   */
  LTE,

  /**
   * Greater-than over integers and rationals.
   */
  GT,

  /**
   * Greater-than-or-equal over integers and rationals.
   */
  GTE,

  /**
   * Equality over integers and rationals.
   * Binary equality is modelled with {@code IFF}.
   */
  EQ,

  /**
   * Solvers support a lot of different built-in theories.
   * We enforce standardization only across a small subset.
   */
  OTHER
}
