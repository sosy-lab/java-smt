// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;
import org.sosy_lab.java_smt.solvers.opensmt.api.Logic;
import org.sosy_lab.java_smt.solvers.opensmt.api.PTRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SymRef;

@SuppressWarnings("MethodTypeParameterName")
public class OpenSmtArrayFormulaManager
    extends AbstractArrayFormulaManager<PTRef, SRef, Logic, SymRef> {

  private final Logic logic;

  public OpenSmtArrayFormulaManager(OpenSmtFormulaCreator pFormulaCreator) {
    super(pFormulaCreator);
    logic = pFormulaCreator.getEnv();
  }

  @Override
  protected PTRef select(PTRef pArray, PTRef pIndex) {
    return logic.mkSelect(pArray, pIndex);
  }

  @Override
  protected PTRef store(PTRef pArray, PTRef pIndex, PTRef pValue) {
    return logic.mkStore(pArray, pIndex, pValue);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> PTRef internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    final SRef osmtArrayType = toSolverType(FormulaType.getArrayType(pIndexType, pElementType));
    return getFormulaCreator().makeVariable(osmtArrayType, pName);
  }

  @Override
  protected <TI extends Formula, TE extends Formula> PTRef internalMakeArray(
      FormulaType<TI> pIndexType, FormulaType<TE> pElementType, PTRef defaultElement) {
    throw new UnsupportedOperationException();
  }

  @Override
  protected PTRef equivalence(PTRef pArray1, PTRef pArray2) {
    return logic.mkEq(pArray1, pArray2);
  }
}
