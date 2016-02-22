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
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.api.QuantifiedFormulaManager.Quantifier;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Base class for visitors for boolean formulas that recursively transform
 * boolean formulas.
 *
 * <p>This class ensures that each subtree of the formula
 * is visited only once.
 * To ensure this for subclasses, they need to call
 * {@link #visitIfNotSeen(BooleanFormula)} or
 * {@link #visitIfNotSeen(List)}.
 *
 * <p><b>WARNING:</b> transforming very large formulas with this class will lead
 * to {@link StackOverflowError}.
 */
public abstract class BooleanFormulaTransformationVisitor
    implements BooleanFormulaVisitor<BooleanFormula> {

  private final BooleanFormulaManager bfmgr;
  private final FormulaManager manager;

  private final Map<BooleanFormula, BooleanFormula> cache;

  protected BooleanFormulaTransformationVisitor(
      FormulaManager pFmgr, Map<BooleanFormula, BooleanFormula> pCache) {
    bfmgr = pFmgr.getBooleanFormulaManager();
    manager = pFmgr;

    cache = pCache;
  }

  protected final BooleanFormula visitIfNotSeen(BooleanFormula f) {
    BooleanFormula out = cache.get(f);
    if (out == null) {
      out = bfmgr.visit(this, f);
      cache.put(f, out);
    }
    return out;
  }

  protected final List<BooleanFormula> visitIfNotSeen(List<BooleanFormula> pOperands) {
    List<BooleanFormula> args = new ArrayList<>(pOperands.size());
    for (BooleanFormula arg : pOperands) {
      args.add(visitIfNotSeen(arg));
    }
    return args;
  }

  @Override
  public BooleanFormula visitConstant(boolean value) {
    return bfmgr.makeBoolean(value);
  }

  @Override
  public BooleanFormula visitBoundVar(BooleanFormula var, int deBruijnIdx) {
    return var;
  }

  @Override
  public BooleanFormula visitAtom(BooleanFormula pAtom, FunctionDeclaration decl) {
    return pAtom;
  }

  @Override
  public BooleanFormula visitNot(BooleanFormula pOperand) {
    return bfmgr.not(visitIfNotSeen(pOperand));
  }

  @Override
  public BooleanFormula visitAnd(List<BooleanFormula> pOperands) {
    return bfmgr.and(visitIfNotSeen(pOperands));
  }

  @Override
  public BooleanFormula visitOr(List<BooleanFormula> pOperands) {
    return bfmgr.or(visitIfNotSeen(pOperands));
  }

  @Override
  public BooleanFormula visitXor(BooleanFormula operand1, BooleanFormula operand2) {
    return bfmgr.xor(operand1, operand2);
  }

  @Override
  public BooleanFormula visitEquivalence(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    return bfmgr.equivalence(visitIfNotSeen(pOperand1), visitIfNotSeen(pOperand2));
  }

  @Override
  public BooleanFormula visitImplication(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    return bfmgr.implication(visitIfNotSeen(pOperand1), visitIfNotSeen(pOperand2));
  }

  @Override
  public BooleanFormula visitIfThenElse(
      BooleanFormula pCondition, BooleanFormula pThenFormula, BooleanFormula pElseFormula) {
    return bfmgr.ifThenElse(
        visitIfNotSeen(pCondition), visitIfNotSeen(pThenFormula), visitIfNotSeen(pElseFormula));
  }

  @Override
  public BooleanFormula visitQuantifier(
      Quantifier quantifier,
      BooleanFormula quantifiedAST,
      List<Formula> boundVars, BooleanFormula body) {
    return quantifiedAST;
  }
}
