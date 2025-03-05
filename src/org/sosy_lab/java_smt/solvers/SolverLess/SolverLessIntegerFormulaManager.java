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
  protected SMTLIB2Formula makeNumberImpl(long i) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.INTEGER), String.valueOf(i));
  }

  @Override
  protected SMTLIB2Formula makeNumberImpl(BigInteger i) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.INTEGER), String.valueOf(i));
  }

  @Override
  protected SMTLIB2Formula makeNumberImpl(String i) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.INTEGER), i);
  }

  @Override
  protected SMTLIB2Formula makeNumberImpl(double pNumber) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.INTEGER), String.valueOf(pNumber));
  }

  @Override
  protected SMTLIB2Formula makeNumberImpl(BigDecimal pNumber) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.INTEGER), String.valueOf(pNumber));
  }

  @Override
  protected SMTLIB2Formula makeVariableImpl(String i) {

    SMTLIB2Formula result = new SMTLIB2Formula(new DummyType(DummyType.Type.INTEGER));
    result.setName(i);
    return result;
  }

  @Override
  protected SMTLIB2Formula add(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.INTEGER));
  }

  @Override
  protected SMTLIB2Formula subtract(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.INTEGER));
  }

  @Override
  public FormulaType<IntegerFormula> getFormulaType() {
    return FormulaType.IntegerType;
  }
}
