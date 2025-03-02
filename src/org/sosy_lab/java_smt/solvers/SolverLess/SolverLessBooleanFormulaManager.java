// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.SolverLess;

import java.util.Objects;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

public class SolverLessBooleanFormulaManager
    extends AbstractBooleanFormulaManager<DummyFormula, DummyType, DummyEnv, DummyFunction> {

  public SolverLessBooleanFormulaManager(SolverLessFormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected DummyFormula makeVariableImpl(String pVar) {
    DummyFormula result = new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
    result.setName(pVar);
    return result;
  }

  @Override
  protected DummyFormula makeBooleanImpl(boolean value) {
    return new DummyFormula(value);
  }

  @Override
  protected DummyFormula not(DummyFormula pParam1) {
    if (Objects.equals(pParam1.getValue(), "")) {
      return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
    }
    return new DummyFormula(!Boolean.parseBoolean(pParam1.getValue()));
  }

  @Override
  protected DummyFormula and(DummyFormula pParam1, DummyFormula pParam2) {
    if (Objects.equals(pParam1.getValue(), "") || Objects.equals(pParam2.getValue(), "")) {
      return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
    }
    return new DummyFormula(
        Boolean.logicalAnd(
            Boolean.parseBoolean(pParam1.getValue()), Boolean.parseBoolean(pParam2.getValue())));
  }

  @Override
  protected DummyFormula or(DummyFormula pParam1, DummyFormula pParam2) {
    if (Objects.equals(pParam1.getValue(), "") || Objects.equals(pParam2.getValue(), "")) {
      return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
    }
    return new DummyFormula(
        Boolean.logicalOr(
            Boolean.parseBoolean(pParam1.getValue()), Boolean.parseBoolean(pParam2.getValue())));
  }

  @Override
  protected DummyFormula xor(DummyFormula pParam1, DummyFormula pParam2) {
    if (Objects.equals(pParam1.getValue(), "") || Objects.equals(pParam2.getValue(), "")) {
      return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
    }
    return new DummyFormula(
        Boolean.logicalXor(
            Boolean.parseBoolean(pParam1.getValue()), Boolean.parseBoolean(pParam2.getValue())));
  }

  @Override
  protected DummyFormula equivalence(DummyFormula bits1, DummyFormula bits2) {
    if (Objects.equals(bits1.getValue(), "") || Objects.equals(bits2.getValue(), "")) {
      return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
    }
    return new DummyFormula(
        Boolean.parseBoolean(bits1.getValue()) == Boolean.parseBoolean(bits2.getValue()));
  }

  @Override
  protected boolean isTrue(DummyFormula bits) {
    if (Objects.equals(bits.getValue(), "")) {
      return false;
    }
    return Boolean.parseBoolean(bits.getValue());
  }

  @Override
  protected boolean isFalse(DummyFormula bits) {
    if (Objects.equals(bits.getValue(), "")) {
      return false;
    }
    return !Boolean.parseBoolean(bits.getValue());
  }

  @Override
  protected DummyFormula ifThenElse(DummyFormula cond, DummyFormula f1, DummyFormula f2) {
    if (Objects.equals(cond.getValue(), "")) {
      return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
    }
    if (Boolean.parseBoolean(cond.getValue())) {
      if (Objects.equals(f1.getValue(), "")) {
        return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
      }
      return new DummyFormula(Boolean.parseBoolean(f1.getValue()));
    } else {
      if (Objects.equals(f2.getValue(), "")) {
        return new DummyFormula(new DummyType(DummyType.Type.BOOLEAN));
      }
      return new DummyFormula(Boolean.parseBoolean(f2.getValue()));
    }
  }
}
