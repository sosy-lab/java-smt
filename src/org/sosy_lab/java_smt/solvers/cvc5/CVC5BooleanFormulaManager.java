// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.vectorExpr;
import io.github.cvc5.api.Solver;
import io.github.cvc5.api.Sort;
import io.github.cvc5.api.Term;
import java.util.Collection;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

public class CVC5BooleanFormulaManager
    extends AbstractBooleanFormulaManager<Term, Sort, Solver, Term> {

  private final Term cvc5True;
  private final Term cvc5False;
  private final Solver solver;

  protected CVC5BooleanFormulaManager(CVC5FormulaCreator pCreator) {
    super(pCreator);
    solver = pCreator.getEnv();
    cvc5True = solver.mkTrue();
    cvc5False = solver.mkFalse();
  }

  @Override
  protected Expr makeVariableImpl(String pVar) {
    return formulaCreator.makeVariable(getFormulaCreator().getBoolType(), pVar);
  }

  @Override
  protected Expr makeBooleanImpl(boolean pValue) {
    return exprManager.mkConst(pValue);
  }

  @Override
  protected Expr not(Expr pParam1) {
    return exprManager.mkExpr(Kind.NOT, pParam1);
  }

  @Override
  protected Expr and(Expr pParam1, Expr pParam2) {
    if (isTrue(pParam1)) {
      return pParam2;
    } else if (isTrue(pParam2)) {
      return pParam1;
    } else if (isFalse(pParam1)) {
      return cvc5False;
    } else if (isFalse(pParam2)) {
      return cvc5False;
    } else if (pParam1 == pParam2) {
      return pParam1;
    }
    return exprManager.mkExpr(Kind.AND, pParam1, pParam2);
  }

  @Override
  protected Expr andImpl(Collection<Expr> pParams) {
    vectorExpr vExpr = new vectorExpr();
    for (Expr e : pParams) {
      if (isFalse(e)) {
        return cvc5False;
      }
      if (!isTrue(e)) {
        vExpr.add(e);
      }
    }
    if (vExpr.capacity() == 0) {
      return cvc5True;
    } else if (vExpr.capacity() == 1) {
      return vExpr.get(0);
    } else {
      return exprManager.mkExpr(Kind.AND, vExpr);
    }
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toConjunction() {
    return Collectors.collectingAndThen(Collectors.toList(), this::and);
  }

  @Override
  protected Expr or(Expr pParam1, Expr pParam2) {
    if (isTrue(pParam1)) {
      return cvc5True;
    } else if (isTrue(pParam2)) {
      return cvc5True;
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
    vectorExpr vExpr = new vectorExpr();
    for (Expr e : pParams) {
      if (isTrue(e)) {
        return cvc5True;
      }
      if (!isFalse(e)) {
        vExpr.add(e);
      }
    }
    if (vExpr.capacity() == 0) {
      return cvc5False;
    } else if (vExpr.capacity() == 1) {
      return vExpr.get(0);
    } else {
      return exprManager.mkExpr(Kind.OR, vExpr);
    }
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toDisjunction() {
    return Collectors.collectingAndThen(Collectors.toList(), this::or);
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
  protected boolean isTrue(Expr pBits) {
    return pBits.isConst() && pBits.getConstBoolean();
  }

  @Override
  protected boolean isFalse(Expr pBits) {
    return pBits.isConst() && !pBits.getConstBoolean();
  }

  @Override
  protected Expr ifThenElse(Expr pCond, Expr pF1, Expr pF2) {
    return exprManager.mkExpr(Kind.ITE, pCond, pF1, pF2);
  }
}
