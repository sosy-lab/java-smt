// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.SolverLess;

import java.util.Objects;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

public class SolverLessBooleanFormulaManager
    extends AbstractBooleanFormulaManager<SMTLIB2Formula, DummyType, DummyEnv, DummyFunction> {

  public SolverLessBooleanFormulaManager(SolverLessFormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected SMTLIB2Formula makeVariableImpl(String pVar) {
    SMTLIB2Formula result = new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
    result.setName(pVar);
    return result;
  }

  @Override
  protected SMTLIB2Formula makeBooleanImpl(boolean value) {
    return new SMTLIB2Formula(value);
  }

  @Override
  protected SMTLIB2Formula not(SMTLIB2Formula pParam1) {
    if (Objects.equals(pParam1.getValue(), "")) {
      return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
    }
    return new SMTLIB2Formula(!Boolean.parseBoolean(pParam1.getValue()));
  }

  @Override
  protected SMTLIB2Formula and(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    if (Objects.equals(pParam1.getValue(), "") || Objects.equals(pParam2.getValue(), "")) {
      return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
    }
    return new SMTLIB2Formula(
        Boolean.logicalAnd(
            Boolean.parseBoolean(pParam1.getValue()), Boolean.parseBoolean(pParam2.getValue())));
  }

  @Override
  protected SMTLIB2Formula or(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    if (Objects.equals(pParam1.getValue(), "") || Objects.equals(pParam2.getValue(), "")) {
      return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
    }
    return new SMTLIB2Formula(
        Boolean.logicalOr(
            Boolean.parseBoolean(pParam1.getValue()), Boolean.parseBoolean(pParam2.getValue())));
  }

  @Override
  protected SMTLIB2Formula xor(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    if (Objects.equals(pParam1.getValue(), "") || Objects.equals(pParam2.getValue(), "")) {
      return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
    }
    return new SMTLIB2Formula(
        Boolean.logicalXor(
            Boolean.parseBoolean(pParam1.getValue()), Boolean.parseBoolean(pParam2.getValue())));
  }

  @Override
  protected SMTLIB2Formula equivalence(SMTLIB2Formula bits1, SMTLIB2Formula bits2) {
    if (Objects.equals(bits1.getValue(), "") || Objects.equals(bits2.getValue(), "")) {
      return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
    }
    return new SMTLIB2Formula(
        Boolean.parseBoolean(bits1.getValue()) == Boolean.parseBoolean(bits2.getValue()));
  }

  @Override
  protected boolean isTrue(SMTLIB2Formula bits) {
    if (Objects.equals(bits.getValue(), "")) {
      return false;
    }
    return Boolean.parseBoolean(bits.getValue());
  }

  @Override
  protected boolean isFalse(SMTLIB2Formula bits) {
    if (Objects.equals(bits.getValue(), "")) {
      return false;
    }
    return !Boolean.parseBoolean(bits.getValue());
  }

  @Override
  protected SMTLIB2Formula ifThenElse(SMTLIB2Formula cond, SMTLIB2Formula f1, SMTLIB2Formula f2) {
    if (Objects.equals(cond.getValue(), "")) {
      return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
    }
    if (Boolean.parseBoolean(cond.getValue())) {
      return f1;
    } else {
      return f2;
    }
  }
}
