// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.SLFormulaManager;

@SuppressWarnings({"ClassTypeParameterName", "MethodTypeParameterName"})
public abstract class AbstractSLFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements SLFormulaManager {

  protected AbstractSLFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pCreator) {
    super(pCreator);
  }

  private BooleanFormula wrap(TFormulaInfo pTerm) {
    return getFormulaCreator().encapsulateBoolean(pTerm);
  }

  @Override
  public BooleanFormula makeStar(BooleanFormula f1, BooleanFormula f2) {
    TFormulaInfo param1 = extractInfo(f1);
    TFormulaInfo param2 = extractInfo(f2);
    return wrap(makeStar(param1, param2));
  }

  protected abstract TFormulaInfo makeStar(TFormulaInfo e1, TFormulaInfo e2);

  @Override
  public BooleanFormula makePointsTo(Formula ptr, Formula to) {
    TFormulaInfo param1 = extractInfo(ptr);
    TFormulaInfo param2 = extractInfo(to);
    return wrap(makePointsTo(param1, param2));
  }

  protected abstract TFormulaInfo makePointsTo(TFormulaInfo ptr, TFormulaInfo to);

  @Override
  public BooleanFormula makeMagicWand(BooleanFormula f1, BooleanFormula f2) {
    TFormulaInfo param1 = extractInfo(f1);
    TFormulaInfo param2 = extractInfo(f2);
    return wrap(makeMagicWand(param1, param2));
  }

  protected abstract TFormulaInfo makeMagicWand(TFormulaInfo e1, TFormulaInfo e2);

  @Override
  public <
      AF extends Formula,
      VF extends Formula,
      AT extends FormulaType<AF>,
      VT extends FormulaType<VF>>
  BooleanFormula makeEmptyHeap(AT pAdressType, VT pValueType) {
    final TType adressType = toSolverType(pAdressType);
    final TType valueType = toSolverType(pValueType);
    return wrap(makeEmptyHeap(adressType, valueType));
  }

  protected abstract TFormulaInfo makeEmptyHeap(TType e1, TType e2);

  @Override
  public <AF extends Formula, AT extends FormulaType<AF>> AF makeNilElement(AT pAdressType) {
    final TType type = toSolverType(pAdressType);
    return getFormulaCreator().encapsulate(pAdressType, makeNilElement(type));
  }

  protected abstract TFormulaInfo makeNilElement(TType type);
}