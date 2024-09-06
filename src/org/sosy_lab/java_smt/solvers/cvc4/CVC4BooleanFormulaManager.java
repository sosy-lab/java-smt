// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import com.google.common.collect.Iterables;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.Type;
import edu.stanford.CVC4.vectorExpr;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Set;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

public class CVC4BooleanFormulaManager
    extends AbstractBooleanFormulaManager<Expr, Type, ExprManager, Expr> {

  private final Expr cvc4True;
  private final Expr cvc4False;
  private final ExprManager exprManager;

  protected CVC4BooleanFormulaManager(CVC4FormulaCreator pCreator) {
    super(pCreator);
    exprManager = pCreator.getEnv();
    cvc4True = exprManager.mkConst(true);
    cvc4False = exprManager.mkConst(false);
  }

  @Override
  protected Expr makeVariableImpl(String pVar) {
    return formulaCreator.makeVariable(getFormulaCreator().getBoolType(), pVar);
  }

  @Override
  protected Expr makeBooleanImpl(boolean pValue) {
    return pValue ? cvc4True : cvc4False;
  }

  @Override
  protected Expr not(Expr pParam1) {
    if (isTrue(pParam1)) {
      return cvc4False;
    } else if (isFalse(pParam1)) {
      return cvc4True;
    } else if (pParam1.getKind() == Kind.NOT) {
      return pParam1.getChild(0);
    }
    return exprManager.mkExpr(Kind.NOT, pParam1);
  }

  @Override
  protected Expr and(Expr pParam1, Expr pParam2) {
    if (isTrue(pParam1)) {
      return pParam2;
    } else if (isTrue(pParam2)) {
      return pParam1;
    } else if (isFalse(pParam1)) {
      return cvc4False;
    } else if (isFalse(pParam2)) {
      return cvc4False;
    } else if (pParam1 == pParam2) {
      return pParam1;
    }
    return exprManager.mkExpr(Kind.AND, pParam1, pParam2);
  }

  @Override
  protected Expr andImpl(Collection<Expr> pParams) {
    // CVC4 does not do any simplifications,
    // so we filter "true", short-circuit on "false", and filter out (simple) redundancies.
    final Set<Expr> operands = new LinkedHashSet<>();
    for (final Expr operand : pParams) {
      if (isFalse(operand)) {
        return cvc4False;
      }
      if (!isTrue(operand)) {
        operands.add(operand);
      }
    }
    switch (operands.size()) {
      case 0:
        return cvc4True;
      case 1:
        return Iterables.getOnlyElement(operands);
      default:
        vectorExpr vExpr = new vectorExpr();
        for (Expr e : operands) {
          vExpr.add(e);
        }
        return exprManager.mkExpr(Kind.AND, vExpr);
    }
  }

  @Override
  protected Expr or(Expr pParam1, Expr pParam2) {
    if (isTrue(pParam1)) {
      return cvc4True;
    } else if (isTrue(pParam2)) {
      return cvc4True;
    } else if (isFalse(pParam1)) {
      return pParam2;
    } else if (isFalse(pParam2)) {
      return pParam1;
    } else if (pParam1 == pParam2) {
      return pParam1;
    }
    return exprManager.mkExpr(Kind.OR, pParam1, pParam2);
  }

  @Override
  protected Expr orImpl(Collection<Expr> pParams) {
    // CVC4 does not do any simplifications,
    // so we filter "true", short-circuit on "false", and filter out (simple) redundancies.
    final Set<Expr> operands = new LinkedHashSet<>();
    for (final Expr operand : pParams) {
      if (isTrue(operand)) {
        return cvc4True;
      }
      if (!isFalse(operand)) {
        operands.add(operand);
      }
    }
    switch (operands.size()) {
      case 0:
        return cvc4False;
      case 1:
        return Iterables.getOnlyElement(operands);
      default:
        vectorExpr vExpr = new vectorExpr();
        for (Expr e : operands) {
          vExpr.add(e);
        }
        return exprManager.mkExpr(Kind.OR, vExpr);
    }
  }

  @Override
  protected Expr xor(Expr pParam1, Expr pParam2) {
    return exprManager.mkExpr(Kind.XOR, pParam1, pParam2);
  }

  @Override
  protected Expr equivalence(Expr pBits1, Expr pBits2) {
    return exprManager.mkExpr(Kind.EQUAL, pBits1, pBits2);
  }

  @Override
  protected Expr implication(Expr bits1, Expr bits2) {
    return exprManager.mkExpr(Kind.IMPLIES, bits1, bits2);
  }

  @Override
  protected boolean isTrue(Expr pBits) {
    return pBits.isConst() && pBits.getKind() == Kind.CONST_BOOLEAN && pBits.getConstBoolean();
  }

  @Override
  protected boolean isFalse(Expr pBits) {
    return pBits.isConst() && pBits.getKind() == Kind.CONST_BOOLEAN && !pBits.getConstBoolean();
  }

  @Override
  protected Expr ifThenElse(Expr pCond, Expr pF1, Expr pF2) {
    if (isTrue(pCond)) {
      return pF1;
    } else if (isFalse(pCond)) {
      return pF2;
    } else if (pF1.equals(pF2)) {
      return pF1;
    } else if (isTrue(pF1) && isFalse(pF2)) {
      return pCond;
    } else if (isFalse(pF1) && isTrue(pF2)) {
      return not(pCond);
    }
    return exprManager.mkExpr(Kind.ITE, pCond, pF1, pF2);
  }
}
