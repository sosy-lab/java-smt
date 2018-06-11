/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
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

import com.google.common.collect.ImmutableSet;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;

/** An arbitrary SMT formula. */
public interface Formula {

  /**
   * Avoid using basic mathematical or logical operators of SMT-LIB2 as names for symbols.
   *
   * <p>We do not accept some names as identifiers for variables or UFs, because they easily
   * misguide the user. Most solvers even would allow such identifiers directly, currently only
   * SMTInterpol has problems with some of them. For consistency, we disallow those names for all
   * solvers.
   */
  ImmutableSet<String> BASIC_OPERATORS =
      ImmutableSet.of("!", "+", "-", "*", "/", "=", "<", ">", "<=", ">=");

  /**
   * Avoid using basic keywords of SMT-LIB2 as names for symbols.
   *
   * <p>We do not accept some names as identifiers for variables or UFs, because they easily
   * misguide the user. Most solvers even would allow such identifiers directly, currently only
   * SMTInterpol has problems with some of them. For consistency, we disallow those names for all
   * solvers.
   */
  ImmutableSet<String> SMTLIB2_KEYWORDS =
      ImmutableSet.of("true", "false", "and", "or", "select", "store", "xor", "distinct");

  /**
   * Avoid using escape characters of SMT-LIB2 as part of names for symbols.
   *
   * <p>We do not accept some names as identifiers for variables or UFs, because they easily
   * misguide the user. Most solvers even would allow such identifiers directly, currently only
   * SMTInterpol has problems with some of them. For consistency, we disallow those names for all
   * solvers.
   */
  ImmutableSet<Character> DISALLOWED_CHARACTERS = ImmutableSet.of('|', '\\');

  /**
   * returns an arbitrary representation of the formula, might be human- or machine-readable.
   *
   * <p>We do not guarantee that the returned String is in any way related to the formula. The
   * solver might apply escaping or even un-escaping. A user should not use the returned String for
   * further processing. For analyzing formulas, we recommend to use a {@link FormulaVisitor}.
   */
  @Override
  String toString();

  /**
   * checks whether the other object is a formula of the same structure. Does not apply an expensive
   * SAT-check to check equisatisfiability.
   *
   * <p>Two formulas that are structured in the same way, are determined as "equal". Due to
   * transformations and simplifications, two equisatisfiable formulas with different structure
   * might not be determined as "equal".
   */
  @Override
  boolean equals(Object other);

  /** returns a valid hashCode satisfying the constraints given by {@link #equals}. */
  @Override
  int hashCode();
}
