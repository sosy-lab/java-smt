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

import org.sosy_lab.common.Appender;
import org.sosy_lab.solver.basicimpl.tactics.Tactic;
import org.sosy_lab.solver.visitors.FormulaTransformationVisitor;
import org.sosy_lab.solver.visitors.FormulaVisitor;
import org.sosy_lab.solver.visitors.TraversalProcess;

import java.util.List;
import java.util.Map;

/**
 * FormulaManager class contains all operations which can be performed on
 * formulas.
 */
public interface FormulaManager {

  /**
   * Returns the Integer-Theory.
   * Because most SAT-solvers support automatic casting between Integer- and Rational-Theory,
   * the Integer- and the RationalFormulaManager both return the same Formulas
   * for numeric operations like ADD, SUBTRACT, TIMES, LESSTHAN, EQUAL and others.
   *
   * @throws UnsupportedOperationException If the theory is not supported by the solver.
   */
  IntegerFormulaManager getIntegerFormulaManager();

  /**
   * Returns the Rational-Theory.
   * Because most SAT-solvers support automatic casting between Integer- and Rational-Theory,
   * the Integer- and the RationalFormulaManager both return the same Formulas
   * for numeric operations like ADD, SUBTRACT, TIMES, LESSTHAN, EQUAL, etc.
   *
   * @throws UnsupportedOperationException If the theory is not supported by the solver.
   */
  RationalFormulaManager getRationalFormulaManager();

  /**
   * Returns the Boolean-Theory.
   */
  BooleanFormulaManager getBooleanFormulaManager();

  /**
   * Returns the Array-Theory.
   *
   * @throws UnsupportedOperationException If the theory is not supported by the solver.
   */
  ArrayFormulaManager getArrayFormulaManager();

  /**
   * Returns the Bitvector-Theory.
   *
   * @throws UnsupportedOperationException If the theory is not supported by the solver.
   */
  BitvectorFormulaManager getBitvectorFormulaManager();

  /**
   * Returns the Floating-Point-Theory.
   *
   * @throws UnsupportedOperationException If the theory is not supported by the solver.
   */
  FloatingPointFormulaManager getFloatingPointFormulaManager();

  /**
   * Returns the function for dealing with uninterpreted functions (UFs).
   */
  UFManager getUFManager();

  /**
   * Returns the interface for handling quantifiers.
   *
   * @throws UnsupportedOperationException If the theory is not supported by the solver.
   */
  QuantifiedFormulaManager getQuantifiedFormulaManager();

  /**
   * Create variable of the type equal to {@code formulaType}.
   *
   * @param formulaType the type of the variable.
   * @param name the name of the variable.
   * @return the created variable.
   */
  <T extends Formula> T makeVariable(FormulaType<T> formulaType, String name);

  /**
   * Create a function application to the given list of arguments.
   *
   * @param declaration Function declaration
   * @param args List of arguments
   * @return Constructed formula
   */
  <T extends Formula> T makeApplication(
      FunctionDeclaration<T> declaration, List<? extends Formula> args);

  /**
   * Create a function application to the given list of arguments.
   *
   * @param declaration Function declaration
   * @param args List of arguments
   * @return Constructed formula
   */
  <T extends Formula> T makeApplication(FunctionDeclaration<T> declaration, Formula... args);

  /**
   * Returns the type of the given Formula.
   */
  <T extends Formula> FormulaType<T> getFormulaType(T formula);

  /**
   * Parse a boolean formula given as a String in an SMT-LIB file format.
   *
   * @return The same formula in the internal representation.
   * @throws IllegalArgumentException If the string cannot be parsed.
   */
  BooleanFormula parse(String s) throws IllegalArgumentException;

  /**
   * Serialize an input formula to an SMT-LIB format.
   * Very useful when passing formulas between different solvers.
   *
   * <p>To get a String, simply call {@link Object#toString()}
   * on the returned object.
   * This method is lazy and does not create an output string until the returned
   * object is actually used.
   *
   * @return SMT-LIB formula serialization.
   */
  Appender dumpFormula(BooleanFormula pT);

  /**
   * Apply a tactic which performs formula transformation. The available tactics
   * depend on the used solver.
   */
  BooleanFormula applyTactic(BooleanFormula input, Tactic tactic) throws InterruptedException;

  /**
   * Simplify an input formula, while ensuring equivalence.
   *
   * <p>For solvers that do not provide a simplification API, an original formula
   * is returned.
   *
   * @param input The input formula
   * @return Simplified version of the formula
   */
  <T extends Formula> T simplify(T input) throws InterruptedException;

  /**
   * Visit the formula with a given visitor.
   */
  @CanIgnoreReturnValue
  <R> R visit(FormulaVisitor<R> rFormulaVisitor, Formula f);

  /**
   * Visit the formula recursively with a given {@link FormulaVisitor}.
   *
   * <p>This method guarantees that the traversal is done iteratively,
   * without using Java recursion, and thus is not prone to StackOverflowErrors.
   *
   * <p>Furthermore, this method also guarantees that every equal part of the formula
   * is visited only once. Thus it can be used to traverse DAG-like formulas efficiently.
   */
  void visitRecursively(FormulaVisitor<TraversalProcess> rFormulaVisitor, Formula f);

  /**
   * Visit the formula recursively with a given {@link FormulaVisitor}.
   *
   * <p>This method guarantees that the traversal is done iteratively,
   * without using Java recursion, and thus is not prone to StackOverflowErrors.
   *
   * <p>Furthermore, this method also guarantees that every equal part of the formula
   * is visited only once. Thus it can be used to traverse DAG-like formulas efficiently.
   *
   * @param pFormulaVisitor Transformation described by the user.
   */
  <T extends Formula> T transformRecursively(FormulaTransformationVisitor pFormulaVisitor, T f);

  /**
   * Extract the names of all free variables and UFs in a formula.
   *
   * @param f   The input formula
   * @return    Map from variable names to the corresponding formulas.
   */
  Map<String, Formula> extractVariables(Formula f);

  /**
   * Extract the names of all free variables and UFs in a formula.
   *
   * @param f   The input formula
   * @return    Map from variable names to the corresponding formulas.
   */
  Map<String, Formula> extractVariablesAndUFs(Formula f);

  /**
   * Substitute every occurrence of any item from {@code changeFrom}
   * in formula {@code f} to the corresponding occurrence from {@code changeTo}.
   *
   * <p>E.g. if {@code changeFrom} contains a variable {@code a} and
   * {@code changeTo} contains a variable {@code b} all occurrences of {@code a}
   * will be changed to {@code b} in the returned formula.
   *
   * @param f Formula to change.
   * @param fromToMapping Mapping of old and new formula parts.
   * @return Formula with parts replaced.
   */
  <T extends Formula> T substitute(T f, Map<? extends Formula, ? extends Formula> fromToMapping);

  /**
   * Translates the formula from another context into the context represented by
   * {@code this}.
   * Default implementation relies on string serialization
   * ({@link #dumpFormula(BooleanFormula)} and {@link #parse(String)}),
   * but each solver may implement more efficient translation between its own
   * contexts.
   *
   * @param formula Formula belonging to {@code otherContext}.
   * @param otherContext Formula manager belonging to the other context.
   * @return Formula belonging to {@code this} context.
   */
  BooleanFormula translateFrom(BooleanFormula formula, FormulaManager otherContext);

  /**
   * For a numeral (i.e., non-boolean) equality "x = y",
   * return a list {@code x<=y, x>=y}.
   *
   * <p>Otherwise, return the list consisting of the input formula.
   * Note:
   *  1) Returned list always has one or two elements.
   *  2) Conjunction over the returned list is equivalent to the input formula.
   */
  <T extends Formula> List<T> splitNumeralEqualityIfPossible(T f);
}
