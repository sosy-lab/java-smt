// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.SolverLess;

import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;

public class SolverLessBitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<SMTLIB2Formula, DummyType, DummyEnv, DummyFunction> {

  protected SolverLessBitvectorFormulaManager(
      SolverLessFormulaCreator pSolverLessFormulaCreator,
      SolverLessBooleanFormulaManager pSolverLessBooleanFormulaManager) {
    super(pSolverLessFormulaCreator, pSolverLessBooleanFormulaManager);
  }

  @Override
  protected SMTLIB2Formula makeBitvectorImpl(int length, SMTLIB2Formula pParam1) {
    return new SMTLIB2Formula(length);
  }

  @Override
  protected SMTLIB2Formula toIntegerFormulaImpl(SMTLIB2Formula pI, boolean signed) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.INTEGER));
  }

  @Override
  protected SMTLIB2Formula makeBitvectorImpl(int pLength, long pI) {
    return new SMTLIB2Formula(pLength);
  }

  @Override
  protected SMTLIB2Formula distinctImpl(List<SMTLIB2Formula> pBits) {
    return super.distinctImpl(pBits);
  }

  @Override
  protected SMTLIB2Formula negate(SMTLIB2Formula pParam1) {
    return new SMTLIB2Formula(pParam1.getBitvectorLength());
  }

  @Override
  protected SMTLIB2Formula add(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(Math.max(pParam1.getBitvectorLength(), pParam2.getBitvectorLength()));
  }

  @Override
  protected SMTLIB2Formula subtract(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(Math.max(pParam1.getBitvectorLength(), pParam2.getBitvectorLength()));
  }

  @Override
  protected SMTLIB2Formula divide(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2, boolean signed) {
    return new SMTLIB2Formula(Math.max(pParam1.getBitvectorLength(), pParam2.getBitvectorLength()));
  }

  @Override
  protected SMTLIB2Formula remainder(
      SMTLIB2Formula pParam1, SMTLIB2Formula pParam2, boolean signed) {
    return new SMTLIB2Formula(pParam1.getBitvectorLength());
  }

  @Override
  protected SMTLIB2Formula smodulo(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(pParam1.getBitvectorLength());
  }

  @Override
  protected SMTLIB2Formula multiply(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(Math.max(pParam1.getBitvectorLength(), pParam2.getBitvectorLength()));
  }

  @Override
  protected SMTLIB2Formula equal(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula greaterThan(
      SMTLIB2Formula pParam1, SMTLIB2Formula pParam2, boolean signed) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula greaterOrEquals(
      SMTLIB2Formula pParam1, SMTLIB2Formula pParam2, boolean signed) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula lessThan(
      SMTLIB2Formula pParam1, SMTLIB2Formula pParam2, boolean signed) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula lessOrEquals(
      SMTLIB2Formula pParam1, SMTLIB2Formula pParam2, boolean signed) {
    return new SMTLIB2Formula(new DummyType(DummyType.Type.BOOLEAN));
  }

  @Override
  protected SMTLIB2Formula not(SMTLIB2Formula pParam1) {
    return new SMTLIB2Formula(pParam1.getBitvectorLength());
  }

  @Override
  protected SMTLIB2Formula and(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(Math.max(pParam1.getBitvectorLength(), pParam2.getBitvectorLength()));
  }

  @Override
  protected SMTLIB2Formula or(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(
        Math.max(
            pParam1.getBitvectorLength(),
            pParam2.getBitvectorLength())); // Boolean formulas do not have a length.
  }

  @Override
  protected SMTLIB2Formula xor(SMTLIB2Formula pParam1, SMTLIB2Formula pParam2) {
    return new SMTLIB2Formula(Math.max(pParam1.getBitvectorLength(), pParam2.getBitvectorLength()));
  }

  @Override
  protected SMTLIB2Formula makeBitvectorImpl(int pLength, BigInteger pI) {
    return new SMTLIB2Formula(pLength);
  }

  @Override
  protected SMTLIB2Formula makeVariableImpl(int pLength, String pVar) {
    SMTLIB2Formula result = new SMTLIB2Formula(pLength);
    result.setName(pVar);
    return result;
  }

  @Override
  protected SMTLIB2Formula shiftRight(
      SMTLIB2Formula pNumber, SMTLIB2Formula toShift, boolean signed) {
    return new SMTLIB2Formula(pNumber.getBitvectorLength());
  }

  @Override
  protected SMTLIB2Formula shiftLeft(SMTLIB2Formula pExtract, SMTLIB2Formula pExtract2) {
    return new SMTLIB2Formula(pExtract.getBitvectorLength());
  }

  @Override
  protected SMTLIB2Formula concat(SMTLIB2Formula number, SMTLIB2Formula pAppend) {
    int newLength = number.getBitvectorLength() + pAppend.getBitvectorLength();
    return new SMTLIB2Formula(newLength);
  }

  @Override
  protected SMTLIB2Formula extract(SMTLIB2Formula pNumber, int pMsb, int pLsb) {
    int newLength = pMsb - pLsb + 1;
    return new SMTLIB2Formula(newLength);
  }

  @Override
  protected SMTLIB2Formula extend(SMTLIB2Formula pNumber, int pExtensionBits, boolean pSigned) {
    return new SMTLIB2Formula(pNumber.getBitvectorLength() + pExtensionBits);
  }

  public FormulaType<?> getFormulaType(SMTLIB2Formula formula) {
    if (formula.getFormulaType().isBitvector()) {
      return FormulaType.getBitvectorTypeWithSize(formula.getBitvectorLength());
    }
    return formula.getFormulaTypeForCreator();
  }
}
