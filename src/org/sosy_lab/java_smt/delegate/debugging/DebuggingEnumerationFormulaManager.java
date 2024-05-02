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
import org.sosy_lab.java_smt.api.FormulaType.EnumerationFormulaType;

public class DebuggingEnumerationFormulaManager implements EnumerationFormulaManager {
  private final EnumerationFormulaManager delegate;
  private final DebuggingContext debugging;

  public DebuggingEnumerationFormulaManager(
      EnumerationFormulaManager pDelegate, DebuggingContext pDebugging) {
    delegate = pDelegate;
    debugging = pDebugging;
  }

  @Override
  public EnumerationFormulaType declareEnumeration(String pName, Set<String> ppElementNames) {
    debugging.assertThreadLocal();
    return delegate.declareEnumeration(pName, ppElementNames);
  }

  @Override
  public EnumerationFormula makeConstant(String pName, EnumerationFormulaType pType) {
    debugging.assertThreadLocal();
    EnumerationFormula result = delegate.makeConstant(pName, pType);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public EnumerationFormula makeVariable(String pVar, EnumerationFormulaType pType) {
    debugging.assertThreadLocal();
    EnumerationFormula result = delegate.makeVariable(pVar, pType);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula equivalence(
      EnumerationFormula pEnumeration1, EnumerationFormula pEnumeration2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(pEnumeration1);
    debugging.assertFormulaInContext(pEnumeration2);
    BooleanFormula result = delegate.equivalence(pEnumeration1, pEnumeration2);
    debugging.addFormulaTerm(result);
    return result;
  }
}
