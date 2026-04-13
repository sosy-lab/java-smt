// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

final class LeanSmtBooleanFormulaManager
    extends AbstractBooleanFormulaManager<Long, LeanSmtType, Long, LeanSmtFunctionDecl> {

  LeanSmtBooleanFormulaManager(LeanSmtFormulaCreator pCreator) {
    super(pCreator);
  }

  private LeanSmtFormulaCreator creator() {
    return (LeanSmtFormulaCreator) getFormulaCreator();
  }

  @Override
  protected Long makeVariableImpl(String pVar) {
    return creator().makeVariable(LeanSmtType.BOOL, pVar);
  }

  @Override
  protected Long makeBooleanImpl(boolean pValue) {
    return pValue ? creator().getTrueHandle() : creator().getFalseHandle();
  }

  @Override
  protected Long not(Long pParam1) {
    if (isTrue(pParam1)) {
      return creator().getFalseHandle();
    }
    if (isFalse(pParam1)) {
      return creator().getTrueHandle();
    }
    LeanSmtFormulaCreator.Expr expr = creator().getExpression(pParam1);
    if (expr.kind == LeanSmtFormulaCreator.ExprKind.APPLICATION
        && expr.declarationKind == FunctionDeclarationKind.NOT
        && expr.arguments.size() == 1) {
      return expr.arguments.get(0);
    }
    return creator()
        .makeUnary(
            "not",
            FunctionDeclarationKind.NOT,
            org.sosy_lab.java_smt.api.FormulaType.BooleanType,
            pParam1);
  }

  @Override
  protected Long and(Long pParam1, Long pParam2) {
    if (pParam1.equals(pParam2)) {
      return pParam1;
    }
    if (isFalse(pParam1) || isFalse(pParam2)) {
      return creator().getFalseHandle();
    }
    if (isTrue(pParam1)) {
      return pParam2;
    }
    if (isTrue(pParam2)) {
      return pParam1;
    }
    return creator()
        .makeBinary(
            "and",
            FunctionDeclarationKind.AND,
            org.sosy_lab.java_smt.api.FormulaType.BooleanType,
            pParam1,
            pParam2);
  }

  @Override
  protected Long or(Long pParam1, Long pParam2) {
    if (pParam1.equals(pParam2)) {
      return pParam1;
    }
    if (isTrue(pParam1) || isTrue(pParam2)) {
      return creator().getTrueHandle();
    }
    if (isFalse(pParam1)) {
      return pParam2;
    }
    if (isFalse(pParam2)) {
      return pParam1;
    }
    return creator()
        .makeBinary(
            "or",
            FunctionDeclarationKind.OR,
            org.sosy_lab.java_smt.api.FormulaType.BooleanType,
            pParam1,
            pParam2);
  }

  @Override
  protected Long xor(Long pParam1, Long pParam2) {
    if (pParam1.equals(pParam2)) {
      return creator().getFalseHandle();
    }
    if (isFalse(pParam1)) {
      return pParam2;
    }
    if (isFalse(pParam2)) {
      return pParam1;
    }
    if (isTrue(pParam1)) {
      return not(pParam2);
    }
    if (isTrue(pParam2)) {
      return not(pParam1);
    }
    return creator()
        .makeBinary(
            "xor",
            FunctionDeclarationKind.XOR,
            org.sosy_lab.java_smt.api.FormulaType.BooleanType,
            pParam1,
            pParam2);
  }

  @Override
  protected Long equivalence(Long pBits1, Long pBits2) {
    if (pBits1.equals(pBits2)) {
      return creator().getTrueHandle();
    }
    if (isTrue(pBits1)) {
      return pBits2;
    }
    if (isTrue(pBits2)) {
      return pBits1;
    }
    if (isFalse(pBits1)) {
      return not(pBits2);
    }
    if (isFalse(pBits2)) {
      return not(pBits1);
    }
    return creator()
        .makeBinary(
            "=",
            FunctionDeclarationKind.EQ,
            org.sosy_lab.java_smt.api.FormulaType.BooleanType,
            pBits1,
            pBits2);
  }

  @Override
  protected Long implication(Long bits1, Long bits2) {
    if (bits1.equals(bits2)) {
      return creator().getTrueHandle();
    }
    if (isFalse(bits1) || isTrue(bits2)) {
      return creator().getTrueHandle();
    }
    if (isTrue(bits1)) {
      return bits2;
    }
    if (isFalse(bits2)) {
      return not(bits1);
    }
    return creator()
        .makeBinary(
            "=>",
            FunctionDeclarationKind.IMPLIES,
            org.sosy_lab.java_smt.api.FormulaType.BooleanType,
            bits1,
            bits2);
  }

  @Override
  protected boolean isTrue(Long pBits) {
    return pBits.equals(creator().getTrueHandle());
  }

  @Override
  protected boolean isFalse(Long pBits) {
    return pBits.equals(creator().getFalseHandle());
  }

  @Override
  protected Long ifThenElse(Long pCond, Long pF1, Long pF2) {
    if (isTrue(pCond)) {
      return pF1;
    }
    if (isFalse(pCond)) {
      return pF2;
    }
    if (pF1.equals(pF2)) {
      return pF1;
    }
    if (creator().getFormulaType(pF1).isBooleanType()) {
      if (isTrue(pF1) && isFalse(pF2)) {
        return pCond;
      }
      if (isFalse(pF1) && isTrue(pF2)) {
        return not(pCond);
      }
    }
    return creator()
        .makeTernary(
            "ite",
            FunctionDeclarationKind.ITE,
            creator().getFormulaType(pF1),
            pCond,
            pF1,
            pF2);
  }
}
