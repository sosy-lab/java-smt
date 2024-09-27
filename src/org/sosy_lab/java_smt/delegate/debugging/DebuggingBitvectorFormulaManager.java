// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

public class DebuggingBitvectorFormulaManager implements BitvectorFormulaManager {
  private final BitvectorFormulaManager delegate;
  private final DebuggingAssertions debugging;

  public DebuggingBitvectorFormulaManager(
      BitvectorFormulaManager pDelegate, DebuggingAssertions pDebugging) {
    delegate = checkNotNull(pDelegate);
    debugging = pDebugging;
  }

  @Override
  public BitvectorFormula makeBitvector(int length, long pI) {
    debugging.assertThreadLocal();
    BitvectorFormula result = delegate.makeBitvector(length, pI);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula makeBitvector(int length, BigInteger pI) {
    debugging.assertThreadLocal();
    BitvectorFormula result = delegate.makeBitvector(length, pI);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula makeBitvector(int length, IntegerFormula pI) {
    debugging.assertThreadLocal();
    BitvectorFormula result = delegate.makeBitvector(length, pI);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public IntegerFormula toIntegerFormula(BitvectorFormula pI, boolean signed) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(pI);
    IntegerFormula result = delegate.toIntegerFormula(pI, signed);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula makeVariable(int length, String pVar) {
    debugging.assertThreadLocal();
    BitvectorFormula result = delegate.makeVariable(length, pVar);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula makeVariable(BitvectorType type, String pVar) {
    debugging.assertThreadLocal();
    BitvectorFormula result = delegate.makeVariable(type, pVar);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public int getLength(BitvectorFormula number) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    return delegate.getLength(number);
  }

  @Override
  public BitvectorFormula negate(BitvectorFormula number) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    BitvectorFormula result = delegate.negate(number);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula add(BitvectorFormula number1, BitvectorFormula number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BitvectorFormula result = delegate.add(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula subtract(BitvectorFormula number1, BitvectorFormula number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BitvectorFormula result = delegate.subtract(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula divide(
      BitvectorFormula numerator, BitvectorFormula denominator, boolean signed) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(numerator);
    debugging.assertFormulaInContext(denominator);
    BitvectorFormula result = delegate.divide(numerator, denominator, signed);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula smodulo(BitvectorFormula numerator, BitvectorFormula denominator) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(numerator);
    debugging.assertFormulaInContext(denominator);
    BitvectorFormula result = delegate.smodulo(numerator, denominator);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula remainder(
      BitvectorFormula numerator, BitvectorFormula denominator, boolean signed) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(numerator);
    debugging.assertFormulaInContext(denominator);
    BitvectorFormula result = delegate.remainder(numerator, denominator, signed);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula multiply(BitvectorFormula number1, BitvectorFormula number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BitvectorFormula result = delegate.multiply(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula equal(BitvectorFormula number1, BitvectorFormula number2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BooleanFormula result = delegate.equal(number1, number2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula greaterThan(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BooleanFormula result = delegate.greaterThan(number1, number2, signed);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula greaterOrEquals(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {

    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BooleanFormula result = delegate.greaterOrEquals(number1, number2, signed);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula lessThan(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BooleanFormula result = delegate.lessThan(number1, number2, signed);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula lessOrEquals(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number1);
    debugging.assertFormulaInContext(number2);
    BooleanFormula result = delegate.lessOrEquals(number1, number2, signed);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula not(BitvectorFormula bits) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(bits);
    BitvectorFormula result = delegate.not(bits);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula and(BitvectorFormula bits1, BitvectorFormula bits2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(bits1);
    debugging.assertFormulaInContext(bits2);
    BitvectorFormula result = delegate.and(bits1, bits2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula or(BitvectorFormula bits1, BitvectorFormula bits2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(bits1);
    debugging.assertFormulaInContext(bits2);
    BitvectorFormula result = delegate.or(bits1, bits2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula xor(BitvectorFormula bits1, BitvectorFormula bits2) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(bits1);
    debugging.assertFormulaInContext(bits2);
    BitvectorFormula result = delegate.xor(bits1, bits2);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula shiftRight(
      BitvectorFormula number, BitvectorFormula toShift, boolean signed) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    debugging.assertFormulaInContext(toShift);
    BitvectorFormula result = delegate.shiftRight(number, toShift, signed);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula shiftLeft(BitvectorFormula number, BitvectorFormula toShift) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    debugging.assertFormulaInContext(toShift);
    BitvectorFormula result = delegate.shiftLeft(number, toShift);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula rotateLeft(BitvectorFormula number, int toRotate) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    BitvectorFormula result = delegate.rotateLeft(number, toRotate);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula rotateLeft(BitvectorFormula number, BitvectorFormula toRotate) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    debugging.assertFormulaInContext(toRotate);
    BitvectorFormula result = delegate.rotateLeft(number, toRotate);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula rotateRight(BitvectorFormula number, int toRotate) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    BitvectorFormula result = delegate.rotateRight(number, toRotate);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula rotateRight(BitvectorFormula number, BitvectorFormula toRotate) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    debugging.assertFormulaInContext(toRotate);
    BitvectorFormula result = delegate.rotateRight(number, toRotate);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula concat(BitvectorFormula prefix, BitvectorFormula suffix) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(prefix);
    debugging.assertFormulaInContext(suffix);
    BitvectorFormula result = delegate.concat(prefix, suffix);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula extract(BitvectorFormula number, int msb, int lsb) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    BitvectorFormula result = delegate.extract(number, msb, lsb);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BitvectorFormula extend(BitvectorFormula number, int extensionBits, boolean signed) {
    debugging.assertThreadLocal();
    debugging.assertFormulaInContext(number);
    BitvectorFormula result = delegate.extend(number, extensionBits, signed);
    debugging.addFormulaTerm(result);
    return result;
  }

  @Override
  public BooleanFormula distinct(List<BitvectorFormula> pBits) {
    debugging.assertThreadLocal();
    for (BitvectorFormula t : pBits) {
      debugging.assertFormulaInContext(t);
    }
    BooleanFormula result = delegate.distinct(pBits);
    debugging.addFormulaTerm(result);
    return result;
  }
}
