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

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.QuantifiedFormulaManager;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;

import java.util.List;

/**
 * Visitor iterating through the boolean part of the formula.
 * Use {@link BooleanFormulaManager#visit(BooleanFormulaVisitor, BooleanFormula)}
 * for visiting formulas.
 *
 * @param <R> Desired return type.
 */
public interface BooleanFormulaVisitor<R> {

  /**
   * Visit a constant with a given value.
   *
   * @see BooleanFormulaManager#makeBoolean
   */
  R visitConstant(boolean value);

  /**
   * Visit a boolean variable bound by a quantifier.
   */
  R visitBoundVar(BooleanFormula var, int deBruijnIdx);

  /**
   * Visit a NOT-expression.
   *
   * @param operand Negated term.
   *
   * @see BooleanFormulaManager#not
   */
  R visitNot(BooleanFormula operand);

  /**
   * Visit an AND-expression.
   *
   * @see BooleanFormulaManager#and
   */
  R visitAnd(List<BooleanFormula> operands);

  /**
   * Visit an OR-expression.
   *
   * @see BooleanFormulaManager#or
   */
  R visitOr(List<BooleanFormula> operands);

  /**
   * Visit a XOR-expression.
   *
   * @see BooleanFormulaManager#xor
   */
  R visitXor(BooleanFormula operand1, BooleanFormula operand2);

  /**
   * Visit an equivalence between two formulas of boolean sort:
   * {@code operand1 = operand2}
   *
   * @see BooleanFormulaManager#equivalence
   */
  R visitEquivalence(BooleanFormula operand1, BooleanFormula operand2);

  /**
   * Visit an implication.
   *
   * @see BooleanFormulaManager#implication
   */
  R visitImplication(BooleanFormula operand1, BooleanFormula operand2);

  /**
   * Visit an if-then-else expression.
   *
   * @see BooleanFormulaManager#ifThenElse
   */
  R visitIfThenElse(
      BooleanFormula condition, BooleanFormula thenFormula, BooleanFormula elseFormula);

  /**
   * Visit a quantifier: forall- or exists-.
   *
   * @param quantifier Quantifier type: FORALL- or EXISTS-
   * @param quantifiedAST AST of the quantified node.
   *                      Provided because it is difficult to re-create from the parameters.
   * @param boundVars Variables bound by this quantifier.
   * @param body Body of the quantified expression.
   *
   * @see QuantifiedFormulaManager#mkQuantifier
   * @see QuantifiedFormulaManager#forall
   * @see QuantifiedFormulaManager#exists
   */
  R visitQuantifier(Quantifier quantifier,
                    BooleanFormula quantifiedAST,
                    List<Formula> boundVars,
                    BooleanFormula body);

  /**
   * Visit an SMT atom.
   * An atom can be a theory expression, constant, or a variable.
   *
   * <p>This is anything with a boolean sort which is not covered by the cases
   * above.
   */
  R visitAtom(BooleanFormula atom, FunctionDeclaration<BooleanFormula> funcDecl);
}
