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

import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.SLFormulaManager;

@SuppressWarnings("UnusedVariable")
public class PortfolioSLFormulaManager implements SLFormulaManager {

  private final PortfolioFormulaCreator creator;

  public PortfolioSLFormulaManager(PortfolioFormulaCreator pCreator) {
    creator = pCreator;
  }

  @Override
  public BooleanFormula makeStar(BooleanFormula f1, BooleanFormula f2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public <AF extends Formula, VF extends Formula> BooleanFormula makePointsTo(AF ptr, VF to) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public BooleanFormula makeMagicWand(BooleanFormula f1, BooleanFormula f2) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public <
          AF extends Formula,
          VF extends Formula,
          AT extends FormulaType<AF>,
          VT extends FormulaType<VF>>
      BooleanFormula makeEmptyHeap(AT pAdressType, VT pValueType) {
    throw new UnsupportedOperationException("implement me");
  }

  @Override
  public <AF extends Formula, AT extends FormulaType<AF>> AF makeNilElement(AT pAdressType) {
    throw new UnsupportedOperationException("implement me");
  }
}
