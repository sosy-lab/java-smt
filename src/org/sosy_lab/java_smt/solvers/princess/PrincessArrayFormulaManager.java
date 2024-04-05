// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import ap.parser.IExpression;
import ap.parser.ITerm;
import ap.theories.arrays.ExtArray.ArraySort;
import ap.types.Sort;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

@SuppressWarnings("MethodTypeParameterName")
class PrincessArrayFormulaManager
    extends AbstractArrayFormulaManager<
        IExpression, Sort, PrincessEnvironment, PrincessFunctionDeclaration> {

  private final PrincessEnvironment env;

  PrincessArrayFormulaManager(
      FormulaCreator<IExpression, Sort, PrincessEnvironment, PrincessFunctionDeclaration>
          pFormulaCreator) {
    super(pFormulaCreator);
    env = pFormulaCreator.getEnv();
  }

  @Override
  protected IExpression select(IExpression pArray, IExpression pIndex) {
    return env.makeSelect((ITerm) pArray, (ITerm) pIndex);
  }

  @Override
  protected IExpression store(IExpression pArray, IExpression pIndex, IExpression pValue) {
    return env.makeStore((ITerm) pArray, (ITerm) pIndex, (ITerm) pValue);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> IExpression internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    final Sort arrayType = toSolverType(FormulaType.getArrayType(pIndexType, pElementType));
    return getFormulaCreator().makeVariable(arrayType, pName);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> IExpression internalMakeArray(
      FormulaType<TI> pIndexType, FormulaType<TE> pElementType, IExpression elseElem) {
    final Sort arrayType = toSolverType(FormulaType.getArrayType(pIndexType, pElementType));
    return env.makeConstArray((ArraySort) arrayType, (ITerm) elseElem);
  }

  @Override
  protected IExpression equivalence(IExpression pArray1, IExpression pArray2) {
    return ap.parser.IExpression.Eq$.MODULE$.apply((ITerm) pArray1, (ITerm) pArray2);
  }
}
