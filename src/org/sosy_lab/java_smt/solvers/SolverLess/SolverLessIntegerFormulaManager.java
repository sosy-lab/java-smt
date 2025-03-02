// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.SolverLess;

import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

public class SolverLessIntegerFormulaManager
    extends SolverLessNumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {

  public SolverLessIntegerFormulaManager(SolverLessFormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected DummyFormula makeNumberImpl(long i) {
    return new DummyFormula(new DummyType(DummyType.Type.INTEGER), String.valueOf(i));
  }

  @Override
  protected DummyFormula makeNumberImpl(BigInteger i) {
    return new DummyFormula(new DummyType(DummyType.Type.INTEGER), String.valueOf(i));
  }

  @Override
  protected DummyFormula makeNumberImpl(String i) {
    return new DummyFormula(new DummyType(DummyType.Type.INTEGER), i);
  }

  @Override
  protected DummyFormula makeNumberImpl(double pNumber) {
    return new DummyFormula(new DummyType(DummyType.Type.INTEGER), String.valueOf(pNumber));
  }

  @Override
  protected DummyFormula makeNumberImpl(BigDecimal pNumber) {
    return new DummyFormula(new DummyType(DummyType.Type.INTEGER), String.valueOf(pNumber));
  }

  @Override
  protected DummyFormula makeVariableImpl(String i) {

    DummyFormula result = new DummyFormula(new DummyType(DummyType.Type.INTEGER));
    result.setName(i);
    return result;
  }

  @Override
  protected DummyFormula add(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(DummyType.Type.INTEGER));
  }

  @Override
  protected DummyFormula subtract(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(new DummyType(DummyType.Type.INTEGER));
  }

  @Override
  public FormulaType<IntegerFormula> getFormulaType() {
    return FormulaType.IntegerType;
  }
}
