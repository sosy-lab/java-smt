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
package org.sosy_lab.solver.z3java;

import com.microsoft.z3.ArrayExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.solver.basicimpl.AbstractArrayFormulaManager;

class Z3ArrayFormulaManager extends AbstractArrayFormulaManager<Expr, Sort, Context> {

  private final Context z3context;

  Z3ArrayFormulaManager(Z3FormulaCreator creator) {
    super(creator);
    this.z3context = creator.getEnv();
  }

  private static ArrayExpr toAE(Expr e) {
    return (ArrayExpr) e;
  }

  @Override
  protected Expr select(Expr pArray, Expr pIndex) {
    return z3context.mkSelect(toAE(pArray), pIndex);
  }

  @Override
  protected Expr store(Expr pArray, Expr pIndex, Expr pValue) {
    return z3context.mkStore(toAE(pArray), pIndex, pValue);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> Expr internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {

    final ArrayFormulaType<TI, TE> arrayFormulaType =
        FormulaType.getArrayType(pIndexType, pElementType);
    final Sort z3ArrayType = toSolverType(arrayFormulaType);

    return getFormulaCreator().makeVariable(z3ArrayType, pName);
  }

  @Override
  protected Expr equivalence(Expr pArray1, Expr pArray2) {
    return z3context.mkEq(toAE(pArray1), toAE(pArray2));
  }
}
