// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.SolverLess;

import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;

public class SolverLessRationalFormulaManager
    extends SolverLessNumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {

  public SolverLessRationalFormulaManager(SolverLessFormulaCreator creator) {
    super(creator);
  }

  @Override
  protected DummyFormula makeNumberImpl(long i) {
    return new DummyFormula(new DummyType(DummyType.Type.RATIONAL), Long.toString(i));
  }

  @Override
  protected DummyFormula makeNumberImpl(BigInteger i) {
    return new DummyFormula(new DummyType(DummyType.Type.RATIONAL), i.toString());
  }

  @Override
  protected DummyFormula makeNumberImpl(String i) {
    return new DummyFormula(new DummyType(DummyType.Type.RATIONAL), i);
  }

  @Override
  protected DummyFormula makeNumberImpl(double pNumber) {
    return new DummyFormula(new DummyType(DummyType.Type.RATIONAL), Double.toString(pNumber));
  }

  @Override
  protected DummyFormula makeNumberImpl(BigDecimal pNumber) {
    return new DummyFormula(new DummyType(DummyType.Type.RATIONAL), pNumber.toPlainString());
  }

  @Override
  protected DummyFormula makeVariableImpl(String i) {
    DummyFormula result = new DummyFormula(new DummyType(DummyType.Type.RATIONAL));
    result.setName(i);
    return result;
  }

  @Override
  protected DummyFormula floor(DummyFormula number) {
    return new DummyFormula(
        new DummyType(DummyType.Type.INTEGER),
        String.valueOf(
            Integer.parseInt(String.valueOf((int) Double.parseDouble(number.toString())))));
  }

  @Override
  public FormulaType<RationalFormula> getFormulaType() {
    return FormulaType.RationalType;
  }
}
