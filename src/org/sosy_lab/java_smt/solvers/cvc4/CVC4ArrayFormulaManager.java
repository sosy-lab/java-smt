// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import edu.stanford.CVC4.ArrayStoreAll;
import edu.stanford.CVC4.ArrayType;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.Type;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;

@SuppressWarnings("MethodTypeParameterName")
public class CVC4ArrayFormulaManager
    extends AbstractArrayFormulaManager<Expr, Type, ExprManager, Expr> {

  private final ExprManager exprManager;

  public CVC4ArrayFormulaManager(CVC4FormulaCreator pFormulaCreator) {
    super(pFormulaCreator);
    exprManager = pFormulaCreator.getEnv();
  }

  @Override
  protected Expr select(Expr pArray, Expr pIndex) {
    return exprManager.mkExpr(Kind.SELECT, pArray, pIndex);
  }

  @Override
  protected Expr store(Expr pArray, Expr pIndex, Expr pValue) {
    return exprManager.mkExpr(Kind.STORE, pArray, pIndex, pValue);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> Expr internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    final Type cvc4ArrayType = toSolverType(FormulaType.getArrayType(pIndexType, pElementType));
    return getFormulaCreator().makeVariable(cvc4ArrayType, pName);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> Expr internalMakeArray(
      FormulaType<TI> pIndexType, FormulaType<TE> pElementType, Expr elseElem) {
    final Type cvc4ArrayType = toSolverType(FormulaType.getArrayType(pIndexType, pElementType));
    return exprManager.mkConst(new ArrayStoreAll((ArrayType) cvc4ArrayType, elseElem));
  }

  @Override
  protected Expr equivalence(Expr pArray1, Expr pArray2) {
    return exprManager.mkExpr(Kind.EQUAL, pArray1, pArray2);
  }
}
