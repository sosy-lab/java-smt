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
    extends AbstractNumeralFormulaManager<DummyFormula, DummyType, DummyEnv, T, Y, DummyFunction> {
  public SolverLessNumeralFormulaManager(SolverLessFormulaCreator creator) {
    super(creator, NonLinearArithmetic.APPROXIMATE_FALLBACK);
  }

  @Override
  protected boolean isNumeral(DummyFormula val) {
    return val.getFormulaType().isInteger() || val.getFormulaType().isRational();
  }

  @Override
  protected DummyFormula negate(DummyFormula pParam1) {
    return new DummyFormula(pParam1.getFormulaType());
  }

  @Override
  protected DummyFormula add(DummyFormula pParam1, DummyFormula pParam2) {
    if (pParam1.getFormulaType().isRational() || pParam2.getFormulaType().isRational()) {
      return new DummyFormula(new DummyType(DummyType.Type.RATIONAL));
    }
    return new DummyFormula(new DummyType(DummyType.Type.INTEGER));
  }

  @Override
  protected DummyFormula subtract(DummyFormula pParam1, DummyFormula pParam2) {
    if (pParam1.getFormulaType().isRational() || pParam2.getFormulaType().isRational()) {
      return new DummyFormula(new DummyType(DummyType.Type.RATIONAL));
    }
    return new DummyFormula(new DummyType(DummyType.Type.INTEGER));
  }

  @Override
  protected DummyFormula equal(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected DummyFormula distinctImpl(List<DummyFormula> pNumbers) {
    return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected DummyFormula greaterThan(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected DummyFormula greaterOrEquals(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected DummyFormula lessThan(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected DummyFormula lessOrEquals(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
  }
}
