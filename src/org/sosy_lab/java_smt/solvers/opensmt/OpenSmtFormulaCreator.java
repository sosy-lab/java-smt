// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import opensmt.ArithLogic;
import opensmt.Logic;
import opensmt.OpenSmt;
import opensmt.PTRef;
import opensmt.SRef;
import opensmt.SymRef;
import opensmt.VectorPTRef;
import opensmt.VectorSRef;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.opensmt.OpenSmtFormula.OpenSmtArrayFormula;
import org.sosy_lab.java_smt.solvers.opensmt.OpenSmtFormula.OpenSmtBooleanFormula;
import org.sosy_lab.java_smt.solvers.opensmt.OpenSmtFormula.OpenSmtIntegerFormula;
import org.sosy_lab.java_smt.solvers.opensmt.OpenSmtFormula.OpenSmtRationalFormula;

public class OpenSmtFormulaCreator extends FormulaCreator<PTRef, SRef, OpenSmt, SymRef> {

  protected final Logic osmtLogic;

  OpenSmtFormulaCreator(OpenSmt solver) {
    // FIXME: We need srefs that are independant of the logic. Map to sref_undef if the sort is not
    // supported?
    super(
        solver,
        solver.getLogic().getSort_bool(),
        solver.getLRALogic().getSort_int(),
        solver.getLRALogic().getSort_real(),
        null,
        null);
    osmtLogic = solver.getLogic();
  }

  @Override
  public PTRef extractInfo(Formula pT) {
    OpenSmtFormula osmtFormula = (OpenSmtFormula) pT;
    return osmtFormula.getOsmtTerm();
  }

  @Override
  public PTRef callFunctionImpl(SymRef declaration, List<PTRef> args) {
    return getEnv().getLogic().insertTerm(declaration, new VectorPTRef(args));
  }

  @Override
  public SymRef declareUFImpl(String pName, SRef pReturnType, List<SRef> pArgTypes) {
    return getEnv().getLogic().declareFun(pName, pReturnType, new VectorSRef(pArgTypes));
  }

  // FIXME: This is a bit of a hack. OpenSmt has no way of accessing the element and index types
  // of an array. We just store them here for now. Maaybe there's a better way?
  private Map<SRef, SRef> arrayIndexTypes = new HashMap<SRef, SRef>();
  private Map<SRef, SRef> arrayElementTypes = new HashMap<SRef, SRef>();

  @Override
  public SRef getArrayType(SRef indexType, SRef elementType) {
    SRef array = getEnv().getLogic().getArraySort(indexType, elementType);
    arrayIndexTypes.put(array, indexType);
    arrayElementTypes.put(array, elementType);
    return array;
  }

  @Override
  public SRef getBitvectorType(int bitwidth) {
    throw new UnsupportedOperationException("OpenSMT does not support bitvectors.");
  }

  @Override
  public SymRef getBooleanVarDeclarationImpl(PTRef pPTRef) {
    return getEnv().getLogic().getSymRef(pPTRef);
  }

  @Override
  public SRef getFloatingPointType(FormulaType.FloatingPointType type) {
    throw new UnsupportedOperationException("OpenSMT does not support floating point operations.");
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TD extends Formula, TR extends Formula> FormulaType<TR> getArrayFormulaElementType(
      ArrayFormula<TD, TR> pArray) {
    OpenSmtArrayFormula<TD, TR> array = (OpenSmtArrayFormula<TD, TR>) pArray;
    return array.getElementType();
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TD extends Formula, TR extends Formula> FormulaType<TD> getArrayFormulaIndexType(
      ArrayFormula<TD, TR> pArray) {
    OpenSmtArrayFormula<TD, TR> array = (OpenSmtArrayFormula<TD, TR>) pArray;
    return array.getIndexType();
  }

  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> FormulaType<T> getFormulaType(T pFormula) {
    if (pFormula instanceof ArrayFormula<?, ?>) {
      FormulaType<T> arrayIndexType = getArrayFormulaIndexType((ArrayFormula<T, T>) pFormula);
      FormulaType<T> arrayElementType = getArrayFormulaElementType((ArrayFormula<T, T>) pFormula);
      return (FormulaType<T>) FormulaType.getArrayType(arrayIndexType, arrayElementType);
    }
    return super.getFormulaType(pFormula);
  }

  @Override
  public FormulaType<?> getFormulaType(PTRef pFormula) {
    SRef sort = getEnv().getLogic().getSortRef(pFormula);
    return getFormulaTypeFromTermType(sort);
  }

  private FormulaType<?> getFormulaTypeFromTermType(SRef sort) {
    Logic logic = getEnv().getLogic();
    if (logic.isSortBool(sort)) {
      return FormulaType.BooleanType;
    }
    if (logic.isArraySort(sort)) {
      FormulaType<?> indexType = getFormulaTypeFromTermType(arrayIndexTypes.get(sort));
      FormulaType<?> elementType = getFormulaTypeFromTermType(arrayElementTypes.get(sort));
      return FormulaType.getArrayType(indexType, elementType);
    }
    ArithLogic alogic = getEnv().getLRALogic();
    if (alogic.isSortInt(sort)) {
      return FormulaType.IntegerType;
    }
    if (alogic.isSortReal(sort)) {
      return FormulaType.RationalType;
    }
    throw new AssertionError(String.format("Encountered unhandled Type '%s'.", sort));
  }

  //////
  @SuppressWarnings("unchecked")
  @Override
  public <T extends Formula> T encapsulate(FormulaType<T> pType, PTRef pTerm) {
    assert pType.equals(getFormulaType(pTerm))
            || (pType.equals(FormulaType.RationalType)
                && getFormulaType(pTerm).equals(FormulaType.IntegerType))
        : String.format(
            "Cannot encapsulate formula %s of Type %s as %s", pTerm, getFormulaType(pTerm), pType);
    if (pType.isBooleanType()) {
      return (T) new OpenSmtBooleanFormula(osmtLogic, pTerm);
    }
    if (pType.isIntegerType()) {
      return (T) new OpenSmtIntegerFormula(osmtLogic, pTerm);
    }
    if (pType.isRationalType()) {
      return (T) new OpenSmtRationalFormula(osmtLogic, pTerm);
    }
    if (pType.isArrayType()) {
      ArrayFormulaType<?, ?> arrFt = (ArrayFormulaType<?, ?>) pType;
      return (T)
          new OpenSmtArrayFormula<>(osmtLogic, pTerm, arrFt.getIndexType(), arrFt.getElementType());
    }
    throw new IllegalArgumentException("Cannot create formulas of Type " + pType + " in OpenSMT");
  }

  /*
  private Formula encapsulate(Term pTerm) {
    return encapsulate(getFormulaType(pTerm), pTerm);
  }
  */

  @Override
  public BooleanFormula encapsulateBoolean(PTRef pTerm) {
    assert getFormulaType(pTerm).isBooleanType()
        : String.format(
            "%s is not boolean, but %s (%s)",
            pTerm, osmtLogic.getSortRef(pTerm), getFormulaType(pTerm));
    return new OpenSmtBooleanFormula(osmtLogic, pTerm);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> encapsulateArray(
      PTRef pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    assert getFormulaType(pTerm).equals(FormulaType.getArrayType(pIndexType, pElementType))
        : String.format(
            "%s is no array, but %s (%s)",
            pTerm, osmtLogic.getSortRef(pTerm), getFormulaType(pTerm));
    return new OpenSmtArrayFormula<>(osmtLogic, pTerm, pIndexType, pElementType);
  }
  ///////////
  @Override
  public PTRef makeVariable(SRef type, String varName) {
    return getEnv().getLogic().mkVar(type, varName);
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, PTRef f) {
    // FIXME
    throw new UnsupportedOperationException("OpenSMT does not support visitors.");
  }
}
