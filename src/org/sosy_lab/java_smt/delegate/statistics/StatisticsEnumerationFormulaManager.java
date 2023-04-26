// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.EnumerationFormulaManager;
import org.sosy_lab.java_smt.api.FormulaType.EnumerationFormulaType;

public class StatisticsEnumerationFormulaManager implements EnumerationFormulaManager {

  private final EnumerationFormulaManager delegate;
  private final SolverStatistics stats;

  StatisticsEnumerationFormulaManager(
      EnumerationFormulaManager pDelegate, SolverStatistics pStats) {
    delegate = checkNotNull(pDelegate);
    stats = checkNotNull(pStats);
  }

  @Override
  public EnumerationFormulaType declareEnumeration(String name, Set<String> elementNames) {
    stats.enumerationDeclarations.getAndIncrement();
    return delegate.declareEnumeration(name, elementNames);
  }

  @Override
  public EnumerationFormula makeConstant(String pName, EnumerationFormulaType pType) {
    stats.enumerationOperations.getAndIncrement();
    return delegate.makeConstant(pName, pType);
  }

  @Override
  public EnumerationFormula makeVariable(String pVar, EnumerationFormulaType pType) {
    stats.enumerationOperations.getAndIncrement();
    return delegate.makeVariable(pVar, pType);
  }

  @Override
  public BooleanFormula equivalence(
      EnumerationFormula pEnumeration1, EnumerationFormula pEnumeration2) {
    stats.enumerationOperations.getAndIncrement();
    return delegate.equivalence(pEnumeration1, pEnumeration2);
  }
}
