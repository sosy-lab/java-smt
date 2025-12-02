// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import com.google.common.collect.ImmutableList;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import java.util.Collection;
import java.util.Set;
import java.util.stream.Collector;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

/** Manager for dealing with boolean formulas. */
public interface BooleanFormulaManager {

  /**
   * Returns a {@link BooleanFormula} representing the given value.
   *
   * @param value the boolean value the returned <code>Formula</code> should represent
   * @return a Formula representing the given value
   */
  default BooleanFormula makeBoolean(boolean value) {
    return value ? makeTrue() : makeFalse();
  }

  /** Shortcut for {@code makeBoolean(true)}. */
  BooleanFormula makeTrue();

  /** Shortcut for {@code makeBoolean(false)}. */
  BooleanFormula makeFalse();

  /**
   * Creates a variable with exactly the given name.
   *
   * <p>Please make sure that the given name is valid in SMT-LIB2. Take a look at {@link
   * FormulaManager#isValidName} for further information.
   *
   * <p>This method does not quote or unquote the given name, but uses the plain name "AS IS".
   * {@link Formula#toString} can return a different String than the given one.
   */
  BooleanFormula makeVariable(String pVar);

  /**
   * Creates a formula representing an equivalence of the two arguments.
   *
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
   * Check, if the formula is the formula "TRUE". This does not include a satisfiability check, but
   * only a syntactical matching. However, depending on the SMT solver, there might be some
   * pre-processing of formulas such that trivial cases like "1==1" are recognized and rewritten as
   * "TRUE", and thus such formulas might also be matched.
   */
  boolean isTrue(BooleanFormula formula);

  /**
   * Check, if the formula is the formula "FALSE". This does not include a satisfiability check, but
   * only a syntactical matching. However, depending on the SMT solver, there might be some
   * pre-processing of formulas such that trivial cases like "1==2" are recognized and rewritten as
   * "FALSE", and thus such formulas might also be matched.
   */
  boolean isFalse(BooleanFormula formula);

  /**
   * Creates a formula representing {@code IF cond THEN f1 ELSE f2}.
   *
   * @param cond a Formula
   * @param f1 a Formula
   * @param f2 a Formula
   * @return (IF cond THEN f1 ELSE f2)
   */
  <T extends Formula> T ifThenElse(BooleanFormula cond, T f1, T f2);

  /**
   * Creates a formula representing a negation of the argument.
   *
   * @param bits a Formula
   * @return {@code !bits}
   */
  BooleanFormula not(BooleanFormula bits);

  /**
   * Creates a formula representing an AND of the two arguments.
   *
   * @param bits1 a Formula
   * @param bits2 a Formula
   * @return {@code bits1 & bits2}
   */
  BooleanFormula and(BooleanFormula bits1, BooleanFormula bits2);

  /**
   * @see #and(BooleanFormula, BooleanFormula)
   */
  BooleanFormula and(Collection<BooleanFormula> bits);

  /**
   * @see #and(BooleanFormula, BooleanFormula)
   */
  default BooleanFormula and(BooleanFormula... bits) {
    return and(ImmutableList.copyOf(bits));
  }

  /** Return a stream {@link Collector} that creates a conjunction of all elements in the stream. */
  Collector<BooleanFormula, ?, BooleanFormula> toConjunction();

  /**
   * Creates a formula representing an OR of the two arguments.
   *
   * @param bits1 a Formula
   * @param bits2 a Formula
   * @return {@code bits1 | bits2}
   */
  BooleanFormula or(BooleanFormula bits1, BooleanFormula bits2);

  /**
   * @see #or(BooleanFormula, BooleanFormula)
   */
  BooleanFormula or(Collection<BooleanFormula> bits);

  /**
   * @see #or(BooleanFormula, BooleanFormula)
   */
  default BooleanFormula or(BooleanFormula... bits) {
    return or(ImmutableList.copyOf(bits));
  }

  /** Return a stream {@link Collector} that creates a disjunction of all elements in the stream. */
  Collector<BooleanFormula, ?, BooleanFormula> toDisjunction();

  /** Creates a formula representing XOR of the two arguments. */
  BooleanFormula xor(BooleanFormula bits1, BooleanFormula bits2);

  /** Visit the formula with the given visitor. */
  @CanIgnoreReturnValue
  <R> R visit(BooleanFormula pFormula, BooleanFormulaVisitor<R> visitor);

  /**
   * Visit the formula recursively with a given {@link BooleanFormulaVisitor}.
   *
   * <p>This method guarantees that the traversal is done iteratively, without using Java recursion,
   * and thus is not prone to StackOverflowErrors.
   *
   * <p>Furthermore, this method also guarantees that every equal part of the formula is visited
   * only once. Thus, it can be used to traverse DAG-like formulas efficiently.
   */
  void visitRecursively(BooleanFormula f, BooleanFormulaVisitor<TraversalProcess> rFormulaVisitor);

  /**
   * Visit the formula recursively with a given {@link BooleanFormulaVisitor}. The arguments each
   * visitor method receives are <b>already</b> transformed.
   *
   * <p>This method guarantees that the traversal is done iteratively, without using Java recursion,
   * and thus is not prone to StackOverflowErrors.
   *
   * <p>Furthermore, this method also guarantees that every equal part of the formula is visited
   * only once. Thus, it can be used to traverse DAG-like formulas efficiently.
   */
  BooleanFormula transformRecursively(
      BooleanFormula f, BooleanFormulaTransformationVisitor pVisitor);

  /**
   * Return a set of formulas such that a conjunction over them is equivalent to the input formula.
   *
   * <p>Example output:
   *
   * <ul>
   *   <li>For conjunction {@code A /\ B /\ C}: {@code A, B, C}
   *   <li>For "true": empty set.
   *   <li>For anything else: singleton set consisting of the input formula.
   * </ul>
   *
   * @param flatten If {@code true}, flatten recursively.
   */
  Set<BooleanFormula> toConjunctionArgs(BooleanFormula f, boolean flatten);

  /**
   * Return a set of formulas such that a disjunction over them is equivalent to the input formula.
   *
   * <p>Example output:
   *
   * <ul>
   *   <li>For conjunction {@code A \/ B \/ C}: {@code A, B, C}
   *   <li>For "false": empty set.
   *   <li>For anything else: singleton set consisting of the input formula.
   * </ul>
   *
   * @param flatten If {@code true}, flatten recursively.
   */
  Set<BooleanFormula> toDisjunctionArgs(BooleanFormula f, boolean flatten);
}
