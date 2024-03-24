// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager.checkVariableName;

import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;

@SuppressWarnings({"ClassTypeParameterName", "MethodTypeParameterName"})
public abstract class AbstractArrayFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements ArrayFormulaManager {

  protected AbstractArrayFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pFormulaCreator) {
    super(pFormulaCreator);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <TI extends Formula, TE extends Formula> TE select(
      ArrayFormula<TI, TE> pArray, TI pIndex) {

    final FormulaType<? extends Formula> elementType =
        getFormulaCreator().getArrayFormulaElementType(pArray);
    // Examples:
    //    Array<Bitvector,Bitvector>
    //    Rational

    final TFormulaInfo term = select(extractInfo(pArray), extractInfo(pIndex));

    return (TE) getFormulaCreator().encapsulate(elementType, term);
  }

  protected abstract TFormulaInfo select(TFormulaInfo pArray, TFormulaInfo pIndex);

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> store(
      ArrayFormula<TI, TE> pArray, TI pIndex, TE pValue) {

    final FormulaType<TI> indexType = getFormulaCreator().getArrayFormulaIndexType(pArray);
    final FormulaType<TE> elementType = getFormulaCreator().getArrayFormulaElementType(pArray);

    final TFormulaInfo term = store(extractInfo(pArray), extractInfo(pIndex), extractInfo(pValue));
    return getFormulaCreator().encapsulateArray(term, indexType, elementType);
  }

  protected abstract TFormulaInfo store(
      TFormulaInfo pArray, TFormulaInfo pIndex, TFormulaInfo pValue);

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> makeArray(
      String pName, ArrayFormulaType<TI, TE> type) {
    return makeArray(pName, type.getIndexType(), type.getElementType());
  }

  @Override
  public <
          TI extends Formula,
          TE extends Formula,
          FTI extends FormulaType<TI>,
          FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(String pName, FTI pIndexType, FTE pElementType) {
    checkVariableName(pName);
    final TFormulaInfo namedArrayFormula = internalMakeArray(pName, pIndexType, pElementType);
    return getFormulaCreator().encapsulateArray(namedArrayFormula, pIndexType, pElementType);
  }

  protected abstract <TI extends Formula, TE extends Formula> TFormulaInfo internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType);

  @Override
  public <
          TI extends Formula,
          TE extends Formula,
          FTI extends FormulaType<TI>,
          FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(FTI pIndexType, FTE pElementType) {
    final TFormulaInfo arrayConst = internalMakeArray(pIndexType, pElementType);
    return getFormulaCreator().encapsulateArray(arrayConst, pIndexType, pElementType);
  }

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> makeArray(
      ArrayFormulaType<TI, TE> type) {
    final TFormulaInfo arrayConst = internalMakeArray(type.getIndexType(), type.getElementType());
    return getFormulaCreator()
        .encapsulateArray(arrayConst, type.getIndexType(), type.getElementType());
  }

  @Override
  public <
          TI extends Formula,
          TE extends Formula,
          FTI extends FormulaType<TI>,
          FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(TE elseElem, FTI pIndexType, FTE pElementType) {
    final TFormulaInfo arrayConst =
        internalMakeArray(extractInfo(elseElem), pIndexType, pElementType);
    return getFormulaCreator().encapsulateArray(arrayConst, pIndexType, pElementType);
  }

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> makeArray(
      TE elseElem, ArrayFormulaType<TI, TE> type) {
    final TFormulaInfo arrayConst =
        internalMakeArray(extractInfo(elseElem), type.getIndexType(), type.getElementType());
    return getFormulaCreator()
        .encapsulateArray(arrayConst, type.getIndexType(), type.getElementType());
  }

  protected <TI extends Formula, TE extends Formula> TFormulaInfo internalMakeArray(
      FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    return internalMakeArray("__unnamed_array", pIndexType, pElementType);
  }

  protected <TI extends Formula, TE extends Formula> TFormulaInfo internalMakeArray(
      TFormulaInfo elseElem, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    throw new UnsupportedOperationException("Initialized arrays are not supported.");
  }

  @Override
  public <TI extends Formula> FormulaType<TI> getIndexType(ArrayFormula<TI, ?> pArray) {
    return getFormulaCreator().getArrayFormulaIndexType(pArray);
  }

  @Override
  public <TE extends Formula> FormulaType<TE> getElementType(ArrayFormula<?, TE> pArray) {
    return getFormulaCreator().getArrayFormulaElementType(pArray);
  }

  @Override
  public <TI extends Formula, TE extends Formula> BooleanFormula equivalence(
      ArrayFormula<TI, TE> pArray1, ArrayFormula<TI, TE> pArray2) {
    return getFormulaCreator()
        .encapsulateBoolean(equivalence(extractInfo(pArray1), extractInfo(pArray2)));
  }

  protected abstract TFormulaInfo equivalence(TFormulaInfo pArray1, TFormulaInfo pArray2);
}
