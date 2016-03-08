/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.api;

import com.google.errorprone.annotations.CanIgnoreReturnValue;

import org.sosy_lab.solver.visitors.BooleanFormulaTransformationVisitor;
import org.sosy_lab.solver.visitors.BooleanFormulaVisitor;
import org.sosy_lab.solver.visitors.TraversalProcess;

import java.util.Collection;

/**
 * Manager for dealing with boolean formulas.
 */
public interface BooleanFormulaManager {

  /**
   * Returns a {@link BooleanFormula} representing the given value.
   *
   * @param value the boolean value the returned <code>Formula</code> should represent
   * @return a Formula representing the given value
   */
  BooleanFormula makeBoolean(boolean value);

  BooleanFormula makeVariable(String pVar);

  /**
   * Creates a formula representing an equivalence of the two arguments.
   * @param formula1 a Formula
   * @param formula2 a Formula
   * @return {@code formula1 <-> formula2}
   */
  BooleanFormula equivalence(BooleanFormula formula1, BooleanFormula formula2);

  /**
   * @return {@code formula1 => formula2}.
   */
  BooleanFormula implication(BooleanFormula formula1, BooleanFormula formula2);

  /**
   * Check, if the formula is the formula "TRUE".
   * This does not include a satisfiability check,
   * but only a syntactical matching.
   * However, depending on the SMT solver,
   * there might be some pre-processing of formulas such that trivial cases
   * like "1==1" are recognized and rewritten as "TRUE",
   * and thus such formulas might also be matched.
   */
  boolean isTrue(BooleanFormula formula);

  /**
   * Check, if the formula is the formula "FALSE".
   * This does not include a satisfiability check,
   * but only a syntactical matching.
   * However, depending on the SMT solver,
   * there might be some pre-processing of formulas such that trivial cases
   * like "1==2" are recognized and rewritten as "FALSE",
   * and thus such formulas might also be matched.
   */
  boolean isFalse(BooleanFormula formula);

  /**
   * Creates a formula representing {@code IF cond THEN f1 ELSE f2}
   * @param cond a Formula
   * @param f1 a Formula
   * @param f2 a Formula
   * @return (IF cond THEN f1 ELSE f2)
   */
  <T extends Formula> T ifThenElse(BooleanFormula cond, T f1, T f2);

  /**
   * Creates a formula representing a negation of the argument.
   * @param bits a Formula
   * @return {@code !bits}
   */
  BooleanFormula not(BooleanFormula bits);

  /**
   * Creates a formula representing an AND of the two arguments.
   * @param bits1 a Formula
   * @param bits2 a Formula
   * @return {@code bits1 & bits2}
   */
  BooleanFormula and(BooleanFormula bits1, BooleanFormula bits2);

  BooleanFormula and(Collection<BooleanFormula> bits);

  /**
   * Creates a formula representing an OR of the two arguments.
   * @param bits1 a Formula
   * @param bits2 a Formula
   * @return {@code bits1 | bits2}
   */
  BooleanFormula or(BooleanFormula bits1, BooleanFormula bits2);

  BooleanFormula or(Collection<BooleanFormula> bits);

  /**
   * Creates a formula representing XOR of the two arguments.
   */
  BooleanFormula xor(BooleanFormula bits1, BooleanFormula bits2);

  /** Visit the formula with the given visitor. */
  @CanIgnoreReturnValue
  <R> R visit(BooleanFormulaVisitor<R> visitor, BooleanFormula formula);

  /**
   * Visit the formula recursively with a given {@link BooleanFormulaVisitor}.
   *
   * <p>This method guarantees that the traversal is done iteratively,
   * without using Java recursion, and thus is not prone to StackOverflowErrors.
   *
   * <p>Furthermore, this method also guarantees that every equal part of the formula
   * is visited only once. Thus it can be used to traverse DAG-like formulas efficiently.
   */
  void visitRecursively(BooleanFormulaVisitor<TraversalProcess> rFormulaVisitor, BooleanFormula f);


  /**
   * Visit the formula recursively with a given {@link BooleanFormulaVisitor}.
   * The arguments each visitor method receives are <b>already</b> transformed.
   *
   * <p>This method guarantees that the traversal is done iteratively,
   * without using Java recursion, and thus is not prone to StackOverflowErrors.
   *
   * <p>Furthermore, this method also guarantees that every equal part of the formula
   * is visited only once. Thus it can be used to traverse DAG-like formulas efficiently.
   */
  BooleanFormula transformRecursively(BooleanFormulaTransformationVisitor pVisitor,
                                             BooleanFormula f);
}
