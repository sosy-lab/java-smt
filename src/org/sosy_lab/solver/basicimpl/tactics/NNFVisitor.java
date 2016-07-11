/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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

package org.sosy_lab.solver.basicimpl.tactics;

import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.BooleanFormulaManager;
import org.sosy_lab.solver.api.FormulaManager;
import org.sosy_lab.solver.api.FunctionDeclaration;
import org.sosy_lab.solver.visitors.BooleanFormulaTransformationVisitor;

import java.util.ArrayList;
import java.util.List;

public class NNFVisitor extends BooleanFormulaTransformationVisitor {
  private final NNFInsideNotVisitor insideNotVisitor;
  private final BooleanFormulaManager bfmgr;

  public NNFVisitor(FormulaManager pFmgr) {
    super(pFmgr);
    bfmgr = pFmgr.getBooleanFormulaManager();
    insideNotVisitor = new NNFInsideNotVisitor(pFmgr);
  }

  @Override
  public BooleanFormula visitNot(BooleanFormula processedOperand) {
    return bfmgr.visit(processedOperand, insideNotVisitor);
  }

  @Override
  public BooleanFormula visitXor(
      BooleanFormula processedOperand1, BooleanFormula processedOperand2) {
    return bfmgr.visit(rewriteXor(processedOperand1, processedOperand2), this);
  }

  private BooleanFormula rewriteXor(BooleanFormula operand1, BooleanFormula operand2) {
    return bfmgr.or(
        bfmgr.and(operand1, bfmgr.not(operand2)), bfmgr.and(bfmgr.not(operand1), operand2));
  }

  @Override
  public BooleanFormula visitEquivalence(
      BooleanFormula processedOperand1, BooleanFormula processedOperand2) {
    return bfmgr.visit(rewriteEquivalence(processedOperand1, processedOperand2), this);
  }

  private BooleanFormula rewriteEquivalence(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    return bfmgr.or(
        bfmgr.and(pOperand1, pOperand2), bfmgr.and(bfmgr.not(pOperand1), bfmgr.not(pOperand2)));
  }

  @Override
  public BooleanFormula visitImplication(
      BooleanFormula processedOperand1, BooleanFormula processedOperand2) {
    return bfmgr.visit(rewriteImplication(processedOperand1, processedOperand2), this);
  }

  private BooleanFormula rewriteImplication(BooleanFormula pOperand1, BooleanFormula pOperand2) {
    return bfmgr.or(bfmgr.not(pOperand1), pOperand2);
  }

  @Override
  public BooleanFormula visitIfThenElse(
      BooleanFormula processedCondition,
      BooleanFormula processedThenFormula,
      BooleanFormula processedElseFormula) {
    return bfmgr.visit(
        rewriteIfThenElse(processedCondition, processedThenFormula, processedElseFormula), this);
  }

  private BooleanFormula rewriteIfThenElse(
      BooleanFormula pCondition, BooleanFormula pThenFormula, BooleanFormula pElseFormula) {
    return bfmgr.or(
        bfmgr.and(pCondition, pThenFormula), bfmgr.and(bfmgr.not(pCondition), pElseFormula));
  }

  private class NNFInsideNotVisitor extends BooleanFormulaTransformationVisitor {

    protected NNFInsideNotVisitor(FormulaManager pFmgr) {
      super(pFmgr);
    }

    @Override
    public BooleanFormula visitConstant(boolean value) {
      return bfmgr.makeBoolean(value);
    }

    @Override
    public BooleanFormula visitAtom(
        BooleanFormula pAtom, FunctionDeclaration<BooleanFormula> decl) {
      return bfmgr.not(pAtom);
    }

    @Override
    public BooleanFormula visitNot(BooleanFormula processedOperand) {
      return bfmgr.visit(processedOperand, NNFVisitor.this);
    }

    @Override
    public BooleanFormula visitAnd(List<BooleanFormula> processedOperands) {
      List<BooleanFormula> newOperands = new ArrayList<>();
      for (BooleanFormula f : processedOperands) {
        newOperands.add(bfmgr.visit(f, this));
      }

      return bfmgr.or(newOperands);
    }

    @Override
    public BooleanFormula visitOr(List<BooleanFormula> processedOperands) {
      List<BooleanFormula> newOperands = new ArrayList<>();
      for (BooleanFormula f : processedOperands) {
        newOperands.add(bfmgr.visit(f, this));
      }

      return bfmgr.and(newOperands);
    }

    @Override
    public BooleanFormula visitXor(
        BooleanFormula processedOperand1, BooleanFormula processedOperand2) {
      return bfmgr.visit(rewriteXor(processedOperand1, processedOperand2), this);
    }

    @Override
    public BooleanFormula visitEquivalence(
        BooleanFormula processedOperand1, BooleanFormula processedOperand2) {
      return bfmgr.visit(rewriteEquivalence(processedOperand1, processedOperand2), this);
    }

    @Override
    public BooleanFormula visitImplication(
        BooleanFormula processedOperand1, BooleanFormula processedOperand2) {

      // Rewrite using primitives.
      return bfmgr.visit(bfmgr.or(bfmgr.not(processedOperand1), processedOperand2), this);
    }

    @Override
    public BooleanFormula visitIfThenElse(
        BooleanFormula processedCondition,
        BooleanFormula processedThenFormula,
        BooleanFormula processedElseFormula) {
      return bfmgr.visit(
          rewriteIfThenElse(processedCondition, processedThenFormula, processedElseFormula), this);
    }
  }
}
