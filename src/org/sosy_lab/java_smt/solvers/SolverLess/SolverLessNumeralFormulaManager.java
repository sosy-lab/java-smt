// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.SolverLess;

import java.util.List;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;

public abstract class SolverLessNumeralFormulaManager<
        T extends NumeralFormula, Y extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
        SMTLIB2Formula, DummyType, DummyEnv, T, Y, DummyFunction> {
  public SolverLessNumeralFormulaManager(SolverLessFormulaCreator creator) {
    super(creator, NonLinearArithmetic.APPROXIMATE_FALLBACK);
  }

  @Override
  protected boolean isNumeral(SMTLIB2Formula val) {
    return val.getFormulaType().isInteger() || val.getFormulaType().isRational();
  }

  @Override
  protected SMTLIB2Formula negate(SMTLIB2Formula pParam1) {
    return new SMTLIB2Formula(pParam1.getFormulaType());
  }

  @Override
  protected SMTLIB2Formula add(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    if (pParam1.getFormulaType().isRational() || pParam2.getFormulaType().isRational()) {
      return new SMTLIB2Formula(new DummyType(DummyType.Type.RATIONAL));
    }
    return new SMTLIB2Formula(new DummyType(DummyType.Type.INTEGER));
  }

  @Override
  protected SMTLIB2Formula subtract(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    if (pParam1.getFormulaType().isRational() || pParam2.getFormulaType().isRational()) {
      return new SMTLIB2Formula(new DummyType(DummyType.Type.RATIONAL));
    }
    return new SMTLIB2Formula(new DummyType(DummyType.Type.INTEGER));
  }

  @Override
  protected SMTLIB2Formula equal(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula distinctImpl(List<SMTLIB2Formula> pNumbers) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula greaterThan(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula greaterOrEquals(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula lessThan(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula lessOrEquals(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }
}
