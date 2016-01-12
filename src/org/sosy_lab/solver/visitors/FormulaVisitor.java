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
package org.sosy_lab.solver.visitors;

import com.google.common.base.Function;

import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;

/**
 * Visitor iterating through entire formula.
 * Use {@link FormulaManager#visit(FormulaVisitor, Formula)} for visiting formulas.
 *
 * @param <R> Desired return type.
 */
public interface FormulaVisitor<R> {

  enum DeclarationKind {

    // Boolean operations
    AND,
    NOT,
    OR,
    IFF,
    ITE,
    XOR,
    IMPLIES,
    DISTINCT,

    // Simple arithmetic,
    // they work across integers and rationals.
    SUB,
    ADD,
    DIV,
    MUL,
    MODULO,
    UF,

    // Simple comparison,
    // work across integers and rationals.
    LT,
    LTE,
    GT,
    GTE,
    EQ,

    /**
     * Solvers support a lot of different built-in theories.
     * We enforce standardization only across a small subset.
     */
    OTHER
  }

  class Declaration {
    private final String name;
    private final DeclarationKind kind;

    private Declaration(String name, DeclarationKind kind) {
      this.name = name;
      this.kind = kind;
    }

    public static Declaration of(String name, DeclarationKind kind) {
      return new Declaration(name, kind);
    }

    public DeclarationKind getKind() {
      return kind;
    }

    public String getName() {
      return name;
    }
  }

  /**
   * Visit a free variable (such as "x", "y" or "z"), not bound by a quantifier.
   * The variable can have any sort (both boolean and non-boolean).
   *
   * @param f Formula representing the variable.
   * @param name Variable name.
   */
  R visitFreeVariable(Formula f, String name);

  /**
   * Visit a variable bound by a quantifier.
   * The variable can have any sort (both boolean and non-boolean).
   *
   * @param f Formula representing the variable.
   * @param name Variable name.
   * @param deBruijnIdx de-Bruijn index of the bound variable, which can be used
   *                    to find the matching quantifier.
   */
  R visitBoundVariable(Formula f, String name, int deBruijnIdx);

  /**
   * Visit a constant, such as "true"/"false" or a numeric constant like "1" or "1.0".
   *
   * @param f Formula representing the constant.
   * @param value The value of the constant. It is either of type {@link Boolean} or of a subtype
   *     of {@link Number}, in most cases a {@link BigInteger}, {@link BigDecimal},
   *     or {@link Rational}.
   *
   * @return An arbitrary return value that is be passed to the caller.
   */
  R visitConstant(Formula f, Object value);

  /**
   * Visit an arbitrary, potentially uninterpreted function.
   * The function can have any sort.
   *
   * @param f Input function.
   * @param args List of arguments
   * @param functionDeclaration Function declaration
   * @param newApplicationConstructor Construct a new function of the same type,
   *                                  with the new arguments as given.
   */
  R visitFunction(
      Formula f,
      List<Formula> args,
      Declaration functionDeclaration,
      Function<List<Formula>, Formula> newApplicationConstructor);

  /**
   * Visit a quantified node.
   *
   * @param f Quantifier formula.
   * @param quantifier Quantifier type: either {@code FORALL} or {@code EXISTS}.
   * @param boundVariables Variables bound by the quantifier
   * @param body Body of the quantifier.
   */
  R visitQuantifier(
      BooleanFormula f, Quantifier quantifier, List<Formula> boundVariables, BooleanFormula body);
}
