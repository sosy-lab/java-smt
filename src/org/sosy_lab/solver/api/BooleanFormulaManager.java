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

import java.util.Collection;

/**
 * Manager for dealing with boolean formulas.
 */
public interface BooleanFormulaManager {
  /**
   * Checks if the given {@link Formula} is a boolean.
   *
   * @param pF the <code>Formula</code> to check
   * @return <code>true</code> if the given <code>Formula</code> is boolean,
   *         <code>false</code> otherwise
   */
  boolean isBoolean(Formula pF);

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

  /** Check, if the formula is of the form "a==b" with two boolean args. */
  boolean isEquivalence(BooleanFormula formula);

  /** Check, if the formula is of the form "a=>b" with two boolean args. */
  boolean isImplication(BooleanFormula formula);

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
   * Creates a formula representing "IF cond THEN f1 ELSE f2"
   * @param cond a Formula
   * @param f1 a Formula
   * @param f2 a Formula
   * @return (IF cond THEN f1 ELSE f2)
   */
  <T extends Formula> T ifThenElse(BooleanFormula cond, T f1, T f2);

  /** Check, if the formula matches ITE(cond,t1,t2) with three args. */
  <T extends Formula> boolean isIfThenElse(T f);

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

  BooleanFormula xor(BooleanFormula bits1, BooleanFormula bits2);

  /** Check, if the formula matches NOT(f) with one boolean arg. */
  boolean isNot(BooleanFormula bits);

  /** Check, if the formula matches AND(a,b) with two (or more) boolean args. */
  boolean isAnd(BooleanFormula bits);

  /** Check, if the formula matches OR(a,b) with two (or more) boolean args. */
  boolean isOr(BooleanFormula bits);

  /** Check, if the formula matches XOR(a,b) with two (or more) boolean args. */
  boolean isXor(BooleanFormula bits);

  /** Apply a tactic which performs formula transformation */
  BooleanFormula applyTactic(BooleanFormula input, Tactic tactic);

  /** Strategies for transforming the formula AST. */
  enum Tactic {
    NNF("nnf", "Convert the formula to NNF"),
    CNF("tseitin-cnf", "Convert the formula to CNF using Tseitin encoding"),
    QE_LIGHT("qe-light", "Perform light quantifier elimination"),
    QE("qe", "Perform quantifier elimination");

    private final String name;
    private final String description;

    Tactic(String pName, String pDescription) {
      name = pName;
      description = pDescription;
    }

    public String getTacticName() {
      return name;
    }

    public String getDescription() {
      return description;
    }
  }
}
