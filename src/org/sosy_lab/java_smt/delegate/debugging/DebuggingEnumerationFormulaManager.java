// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.EnumerationFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType.EnumerationFormulaType;

public class DebuggingEnumerationFormulaManager extends FormulaChecks
    implements EnumerationFormulaManager {
  private final EnumerationFormulaManager delegate;

  public DebuggingEnumerationFormulaManager(
      EnumerationFormulaManager pDelegate, Set<Formula> pLocalFormulas) {
    super(pLocalFormulas);
    delegate = pDelegate;
  }

  @Override
  public EnumerationFormulaType declareEnumeration(String pName, Set<String> ppElementNames) {
    assertThreadLocal();
    return delegate.declareEnumeration(pName, ppElementNames);
  }

  @Override
  public EnumerationFormula makeConstant(String pName, EnumerationFormulaType pType) {
    assertThreadLocal();
    EnumerationFormula result = delegate.makeConstant(pName, pType);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public EnumerationFormula makeVariable(String pVar, EnumerationFormulaType pType) {
    assertThreadLocal();
    EnumerationFormula result = delegate.makeVariable(pVar, pType);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula equivalence(
      EnumerationFormula pEnumeration1, EnumerationFormula pEnumeration2) {
    assertThreadLocal();
    assertFormulaInContext(pEnumeration1);
    assertFormulaInContext(pEnumeration2);
    BooleanFormula result = delegate.equivalence(pEnumeration1, pEnumeration2);
    addFormulaToContext(result);
    return result;
  }
}
