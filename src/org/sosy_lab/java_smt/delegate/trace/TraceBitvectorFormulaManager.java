/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.trace;

import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

public class TraceBitvectorFormulaManager implements BitvectorFormulaManager {

  @Override
  public BitvectorFormula makeBitvector(int length, long pI) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula makeBitvector(int length, BigInteger pI) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula makeBitvector(int length, IntegerFormula pI) {
    throw new UnsupportedOperationException();
  }

  @Override
  public IntegerFormula toIntegerFormula(BitvectorFormula pI, boolean signed) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula makeVariable(int length, String pVar) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula makeVariable(BitvectorType type, String pVar) {
    throw new UnsupportedOperationException();
  }

  @Override
  public int getLength(BitvectorFormula number) {
    return 0;
  }

  @Override
  public BitvectorFormula negate(BitvectorFormula number) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula add(BitvectorFormula number1, BitvectorFormula number2) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula subtract(BitvectorFormula number1, BitvectorFormula number2) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula divide(
      BitvectorFormula dividend, BitvectorFormula divisor, boolean signed) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula smodulo(BitvectorFormula dividend, BitvectorFormula divisor) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula remainder(
      BitvectorFormula dividend, BitvectorFormula divisor, boolean signed) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula multiply(BitvectorFormula number1, BitvectorFormula number2) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanFormula equal(BitvectorFormula number1, BitvectorFormula number2) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanFormula greaterThan(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanFormula greaterOrEquals(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanFormula lessThan(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanFormula lessOrEquals(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula not(BitvectorFormula bits) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula and(BitvectorFormula bits1, BitvectorFormula bits2) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula or(BitvectorFormula bits1, BitvectorFormula bits2) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula xor(BitvectorFormula bits1, BitvectorFormula bits2) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula shiftRight(
      BitvectorFormula number, BitvectorFormula toShift, boolean signed) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula shiftLeft(BitvectorFormula number, BitvectorFormula toShift) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula rotateLeft(BitvectorFormula number, int toRotate) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula rotateLeft(BitvectorFormula number, BitvectorFormula toRotate) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula rotateRight(BitvectorFormula number, int toRotate) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula rotateRight(BitvectorFormula number, BitvectorFormula toRotate) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula concat(BitvectorFormula prefix, BitvectorFormula suffix) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula extract(BitvectorFormula number, int msb, int lsb) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BitvectorFormula extend(BitvectorFormula number, int extensionBits, boolean signed) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanFormula distinct(List<BitvectorFormula> pBits) {
    throw new UnsupportedOperationException();
  }
}
