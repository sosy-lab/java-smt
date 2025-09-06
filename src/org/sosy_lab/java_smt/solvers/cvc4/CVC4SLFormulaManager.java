// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.Type;
import org.sosy_lab.java_smt.basicimpl.AbstractSLFormulaManager;

public class CVC4SLFormulaManager extends AbstractSLFormulaManager<Expr, Type, ExprManager, Expr> {

  private final ExprManager exprManager;

  protected CVC4SLFormulaManager(CVC4FormulaCreator pCreator) {
    super(pCreator);
    exprManager = pCreator.getEnv();
  }

  @Override
  protected Expr makeStar(Expr e1, Expr e2) {
    return exprManager.mkExpr(Kind.SEP_STAR, e1, e2);
  }

  @Override
  protected Expr makePointsTo(Expr pPtr, Expr pTo) {
    return exprManager.mkExpr(Kind.SEP_PTO, pPtr, pTo);
  }

  @Override
  protected Expr makeMagicWand(Expr pE1, Expr pE2) {
    return exprManager.mkExpr(Kind.SEP_WAND, pE1, pE2);
  }

  @Override
  protected Expr makeEmptyHeap(Type pT1, Type pT2) {
    return exprManager.mkExpr(Kind.SEP_EMP, pT1.mkGroundTerm(), pT2.mkGroundTerm());
  }

  @Override
  protected Expr makeNilElement(Type pType) {
    // TODO CVC4 bindings for Java do not support creation of SEP_NIL via mkTerm.
    //  It is unclear whether this method ever worked.
    //  CVC4 is deprecated and we will not investigate here.
    //
    // Executing this method will cause the following exception:
    //     Illegal argument detected: CVC4::Expr CVC4::ExprManager::mkExpr(CVC4::Kind, CVC4::Expr)
    //     `kind' is a bad argument; ... Only operator-style expressions are made with mkExpr();
    //     to make variables and constants, see mkVar(), mkBoundVar(), and mkConst().
    return exprManager.mkExpr(Kind.SEP_NIL, pType.mkGroundTerm());
  }
}
