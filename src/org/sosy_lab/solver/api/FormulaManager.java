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

import org.sosy_lab.common.Appender;
import org.sosy_lab.solver.basicimpl.tactics.Tactic;
import org.sosy_lab.solver.visitors.FormulaVisitor;
import org.sosy_lab.solver.visitors.TraversalProcess;

import java.util.Set;

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
   */
  IntegerFormulaManager getIntegerFormulaManager();

  /**
   * Returns the Rational-Theory.
   * Because most SAT-solvers support automatic casting between Integer- and Rational-Theory,
   * the Integer- and the RationalFormulaManager both return the same Formulas
   * for numeric operations like ADD, SUBTRACT, TIMES, LESSTHAN, EQUAL, etc.
   */
  RationalFormulaManager getRationalFormulaManager();

  /**
   * Returns the Boolean-Theory.
   */
  BooleanFormulaManager getBooleanFormulaManager();

  /**
   * Returns the Array-Theory.
   */
  ArrayFormulaManager getArrayFormulaManager();

  /**
   * Returns the Bitvector-Theory.
   */
  BitvectorFormulaManager getBitvectorFormulaManager();

  /**
   * Returns the Floating-Point-Theory.
   */
  FloatingPointFormulaManager getFloatingPointFormulaManager();

  /**
   * Returns the Function-Theory.
   */
  FunctionFormulaManager getFunctionFormulaManager();

  /**
   * Returns some unsafe traverse methods.
   */
  UnsafeFormulaManager getUnsafeFormulaManager();

  /**
   * Returns the interface for handling quantifiers.
   */
  QuantifiedFormulaManager getQuantifiedFormulaManager();

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
  BooleanFormula applyTactic(BooleanFormula input, Tactic tactic);

  /**
   * Simplify an input formula, while ensuring equivalence.
   *
   * <p>For solvers that do not provide a simplification API, an original formula
   * is returned.
   *
   * @param input The input formula
   * @return Simplified version of the formula
   */
  <T extends Formula> T simplify(T input);

  /**
   * Visit the formula with a given visitor.
   */
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
   * Extract the names of all free variables and UFs in a formula.
   *
   * @param f   The input formula
   * @return    Set of variable names.
   */
  Set<String> extractVariableNames(Formula f);

  /**
   * Extract the names of all free variables and UFs in a formula.
   *
   * @param f   The input formula
   * @return    Set of variable names.
   */
  Set<String> extractFunctionNames(Formula f);
}
