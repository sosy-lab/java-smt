// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Alejandro SerranoMena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager.checkVariableName;

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.StringFormula;
import org.sosy_lab.java_smt.api.StringFormulaManager;

@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractStringFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements StringFormulaManager {

  protected AbstractStringFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pCreator) {
    super(pCreator);
  }

  private StringFormula wrap(TFormulaInfo formulaInfo) {
    return getFormulaCreator().encapsulateString(formulaInfo);
  }

  @Override
  public StringFormula makeString(String value) {
    return wrap(makeStringImpl(value));
  }

  protected abstract TFormulaInfo makeStringImpl(String value);

  @Override
  public StringFormula makeVariable(String pVar) {
    checkVariableName(pVar);
    return wrap(makeVariableImpl(pVar));
  }

  protected abstract TFormulaInfo makeVariableImpl(String pVar);

  @Override
  public StringFormula equal(StringFormula str1, StringFormula str2) {
    TFormulaInfo param1 = extractInfo(str1);
    TFormulaInfo param2 = extractInfo(str2);

    return wrap(equal(param1, param2));
  }

  protected abstract TFormulaInfo equal(TFormulaInfo pParam1, TFormulaInfo pParam2);
}