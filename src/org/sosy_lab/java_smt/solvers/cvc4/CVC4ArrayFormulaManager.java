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
package org.sosy_lab.java_smt.solvers.cvc4;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.Type;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;

public class CVC4ArrayFormulaManager
    extends AbstractArrayFormulaManager<Expr, Type, CVC4Environment, Expr> {
  protected final ExprManager exprManager;

  public CVC4ArrayFormulaManager(CVC4FormulaCreator pFormulaCreator) {
    super(pFormulaCreator);
    exprManager = pFormulaCreator.getExprManager();
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
  protected <TI extends Formula, TE extends Formula> Expr internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    final ArrayFormulaType<TI, TE> arrayFormulaType =
        FormulaType.getArrayType(pIndexType, pElementType);
    final Type cvc4ArrayType = toSolverType(arrayFormulaType);
    ((CVC4FormulaCreator) formulaCreator)
        .arrayTypeMapping.put(
            pName, new Type[] {toSolverType(pIndexType), toSolverType(pElementType)});
    return getFormulaCreator().makeVariable(cvc4ArrayType, pName);
  }

  @Override
  protected Expr equivalence(Expr pArray1, Expr pArray2) {
    return exprManager.mkExpr(Kind.EQUAL, pArray1, pArray2);
  }
}
