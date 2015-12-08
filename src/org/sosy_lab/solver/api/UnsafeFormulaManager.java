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

import java.util.List;
import java.util.Map;

/**
 * This interface contains methods for formula traversal,
 * which generally should be avoided.
 */
public interface UnsafeFormulaManager {

  /**
   * @return arity of the input formula.
   */
  int getArity(Formula f);

  /**
   * @return argument under the given index for the input function.
   */
  Formula getArg(Formula f, int n);

  /**
   * @return whether the given Formula is an atom.
   */
  boolean isAtom(Formula f);

  /**
   * @return whether the given Formula is a variable, either free or quantified
   */
  boolean isVariable(Formula f);

  /**
   * @return whether the given Formula is a free (not quantified) variable.
   */
  boolean isFreeVariable(Formula f);

  /**
   * @return whether the given Formula is a bound (by a quantifier) variable.
   */
  boolean isBoundVariable(Formula f);

  /**
   * @return whether if the given Formula is a Number.
   */
  boolean isNumber(Formula pTt);
  /**
   * @return whether if the given Formula is an uninterpreted function call.
   */
  boolean isUF(Formula f);

  /**
   * @return whether if the given Formula is quantified
   * (either FORALL ..., or EXISTS ...).
   */
  boolean isQuantification(Formula f);

  /**
   * Get the body of the given, quantified, formula.
   *
   * <p>Precondition: {@link #isQuantification(Formula)} returns true for this formula.
   */
  BooleanFormula getQuantifiedBody(Formula pQuantifiedFormula);

  /**
   * Replace the body of a quantified formula.
   *
   * <p>Precondition: {@link #isQuantification(Formula)} returns true for the first parameter.
   */
  BooleanFormula replaceQuantifiedBody(BooleanFormula pF, BooleanFormula pNewBody);

  /**
   * Returns the name of the formula (or function)
   */
  String getName(Formula f);

  /**
   * Replaces the name and the arguments of the given formula.
   * The old and the new name need to be of the same type.
   * If f is a variable, use an empty list of arguments.
   */
  <T extends Formula> T replaceArgsAndName(T f, String newName, List<Formula> args);
  /**
   * Replaces the arguments of the given formula
   */
  <T extends Formula> T replaceArgs(T f, List<Formula> args);

  /**
   * If the given formula is a numeral (i.e., non-boolean) equality "x = y",
   * return a list {@code x<=y, x>=y}.
   *
   * <p>Otherwise, return the unchanged formula.
   * Note:
   *  1) Returned list always has one or two elements.
   *  2) Conjunction over the returned list is equivalent to the input formula.
   */
  <T extends Formula> List<T> splitNumeralEqualityIfPossible(T f);

  /**
   * Substitute every occurrence of any item from {@code changeFrom}
   * in formula {@code f} to the corresponding occurrence from {@code changeTo}.
   *
   * <p>E.g. if {@code changeFrom} contains a variable {@code a} and
   * {@code changeTo} contains a variable {@code b} all occurrences of {@code a}
   * will be changed to {@code b} in the returned formula.
   *
   * @param f Formula to change
   * @param changeFrom List of things to change from.
   * @param changeTo List of things to change to.
   * @return Formula with variables being replaced.
   *
   */
  <T1 extends Formula, T2 extends Formula> T1 substitute(
      T1 f, List<T2> changeFrom, List<T2> changeTo);

  /**
   * Same as {@link #substitute(Formula, List, List)}, but uses a map.
   */
  <T1 extends Formula, T2 extends Formula> T1 substitute(T1 f, Map<T2, T2> fromToMapping);

  /**
   * Simplifies an input formula, while ensuring equivalence.
   *
   * <p>For solvers that do not provide a simplification API, an original formula
   * is returned.
   *
   * @param f The input formula
   * @return Simplified version of the formula
   */
  <T extends Formula> T simplify(T f);
}
