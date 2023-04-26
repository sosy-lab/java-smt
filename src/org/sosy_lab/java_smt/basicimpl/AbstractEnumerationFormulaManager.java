// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager.checkVariableName;

import com.google.common.base.Preconditions;
import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.EnumerationFormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.EnumerationFormulaType;

@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractEnumerationFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements EnumerationFormulaManager {

  AbstractEnumerationFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pFormulaCreator) {
    super(pFormulaCreator);
  }

  private EnumerationFormula wrap(TFormulaInfo pTerm) {
    return getFormulaCreator().encapsulateEnumeration(pTerm);
  }

  private void checkSameEnumerationType(EnumerationFormula pF1, EnumerationFormula pF2) {
    final FormulaType<?> type1 = formulaCreator.getFormulaType(pF1);
    final FormulaType<?> type2 = formulaCreator.getFormulaType(pF2);
    checkArgument(type1 instanceof EnumerationFormulaType);
    checkArgument(type2 instanceof EnumerationFormulaType);
    checkArgument(
        type1.equals(type2),
        "Can't compare element of type %s with element of type %s.",
        type1,
        type2);
  }

  @Override
  public EnumerationFormulaType declareEnumeration(String pName, Set<String> pElementNames) {
    checkVariableName(pName);
    return declareEnumerationImpl(pName, pElementNames);
  }

  protected abstract EnumerationFormulaType declareEnumerationImpl(
      String pName, Set<String> pElementNames);

  @Override
  public EnumerationFormula makeConstant(String pName, EnumerationFormulaType pType) {
    Preconditions.checkArgument(
        pType.getElements().contains(pName),
        "Constant '%s' is not available in the enumeration type '%s'",
        pName,
        pType);
    return wrap(makeConstantImpl(pName, pType));
  }

  protected abstract TFormulaInfo makeConstantImpl(String pName, EnumerationFormulaType pType);

  @Override
  public EnumerationFormula makeVariable(String pVar, EnumerationFormulaType pType) {
    checkVariableName(pVar);
    return wrap(makeVariableImpl(pVar, pType));
  }

  protected abstract TFormulaInfo makeVariableImpl(String pVar, EnumerationFormulaType pType);

  @Override
  public BooleanFormula equivalence(EnumerationFormula pF1, EnumerationFormula pF2) {
    this.checkSameEnumerationType(pF1, pF2);
    return wrapBool(equivalenceImpl(extractInfo(pF1), extractInfo(pF2)));
  }

  protected abstract TFormulaInfo equivalenceImpl(TFormulaInfo f1, TFormulaInfo f2);
}
