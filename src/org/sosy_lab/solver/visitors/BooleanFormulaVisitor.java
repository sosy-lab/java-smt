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

  R visitTrue();

  R visitFalse();

  R visitAtom(BooleanFormula atom);

  R visitNot(BooleanFormula operand);

  R visitAnd(List<BooleanFormula> operands);

  R visitOr(List<BooleanFormula> operand);

  R visitEquivalence(BooleanFormula operand1, BooleanFormula operand2);

  R visitImplication(BooleanFormula operand1, BooleanFormula operand2);

  R visitIfThenElse(
      BooleanFormula condition, BooleanFormula thenFormula, BooleanFormula elseFormula);

  R visitQuantifier(Quantifier quantifier, BooleanFormula body);
}
