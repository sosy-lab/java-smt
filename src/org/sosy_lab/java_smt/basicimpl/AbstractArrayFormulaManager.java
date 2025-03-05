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
    TE result = (TE) getFormulaCreator().encapsulate(elementType, term);
    if (Generator.isLoggingEnabled()) {
      ArrayGenerator.logSelect(result, pArray, pIndex);
    }
    return result;
  }

  protected abstract TFormulaInfo select(TFormulaInfo pArray, TFormulaInfo pIndex);

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> store(
      ArrayFormula<TI, TE> pArray, TI pIndex, TE pValue) {

    final FormulaType<TI> indexType = getFormulaCreator().getArrayFormulaIndexType(pArray);
    final FormulaType<TE> elementType = getFormulaCreator().getArrayFormulaElementType(pArray);

    final TFormulaInfo term = store(extractInfo(pArray), extractInfo(pIndex), extractInfo(pValue));
    ArrayFormula<TI, TE> result =
        getFormulaCreator().encapsulateArray(term, indexType, elementType);
    if (Generator.isLoggingEnabled()) {
      ArrayGenerator.logStore(result, pArray, pIndex, pValue);
    }
    return result;
  }

  protected abstract TFormulaInfo store(
      TFormulaInfo pArray, TFormulaInfo pIndex, TFormulaInfo pValue);

  @Override
  public <
          TI extends Formula,
          TE extends Formula,
          FTI extends FormulaType<TI>,
          FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(String pName, FTI pIndexType, FTE pElementType)
          throws GeneratorException {
    checkVariableName(pName);
    final TFormulaInfo namedArrayFormula = internalMakeArray(pName, pIndexType, pElementType);
    ArrayFormula<TI, TE> result =
        getFormulaCreator().encapsulateArray(namedArrayFormula, pIndexType, pElementType);
    if (Generator.isLoggingEnabled()) {
      ArrayGenerator.logMakeArray(result, pName, pIndexType, pElementType);
    }
    return result;
  }

  @Override
  public <
          TI extends Formula,
          TE extends Formula,
          FTI extends FormulaType<TI>,
          FTE extends FormulaType<TE>>
      ArrayFormula<TI, TE> makeArray(FTI pIndexType, FTE pElementType, TE elseElem) {
    final TFormulaInfo arrayConst =
        internalMakeArray(pIndexType, pElementType, extractInfo(elseElem));
    return getFormulaCreator().encapsulateArray(arrayConst, pIndexType, pElementType);
  }

  protected abstract <TI extends Formula, TE extends Formula> TFormulaInfo internalMakeArray(
      String pName, FormulaType<TI> pIndexType, FormulaType<TE> pElementType);

  protected abstract <TI extends Formula, TE extends Formula> TFormulaInfo internalMakeArray(
      FormulaType<TI> pIndexType, FormulaType<TE> pElementType, TFormulaInfo elseElem);

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
    BooleanFormula result =
        getFormulaCreator()
            .encapsulateBoolean(equivalence(extractInfo(pArray1), extractInfo(pArray2)));
    if (Generator.isLoggingEnabled()) {
      ArrayGenerator.logArrayEquivalence(result, pArray1, pArray2);
    }
    return result;
  }

  protected abstract TFormulaInfo equivalence(TFormulaInfo pArray1, TFormulaInfo pArray2);
}
