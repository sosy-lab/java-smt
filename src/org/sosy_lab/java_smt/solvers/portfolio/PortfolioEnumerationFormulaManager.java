/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.portfolio;

import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.EnumerationFormulaManager;
import org.sosy_lab.java_smt.api.FormulaType.EnumerationFormulaType;

@SuppressWarnings("UnusedVariable")
public class PortfolioEnumerationFormulaManager implements EnumerationFormulaManager {

  private final PortfolioFormulaCreator creator;

  public PortfolioEnumerationFormulaManager(PortfolioFormulaCreator pCreator) {
    creator = pCreator;
  }

  @Override
  public EnumerationFormulaType declareEnumeration(String pName, Set<String> ppElementNames) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public EnumerationFormula makeConstant(String pName, EnumerationFormulaType pType) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public EnumerationFormula makeVariable(String pVar, EnumerationFormulaType pType) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula equivalence(
      EnumerationFormula pEnumeration1, EnumerationFormula pEnumeration2) {
    throw new UnsupportedOperationException("implement me");
  }
}
