/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.parsing;

import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.delegate.parsing.ParsingFormulaManager.SymbolManager;

public class ParsingBitvectorFormulaManager implements BitvectorFormulaManager {
  private final SymbolManager symbolManager;
  private final BitvectorFormulaManager delegate;

  public ParsingBitvectorFormulaManager(
      SymbolManager pSymbolManager, BitvectorFormulaManager pDelegate) {
    symbolManager = pSymbolManager;
    delegate = pDelegate;
  }

  @Override
  public BitvectorFormula makeBitvector(int length, long pI) {
    return delegate.makeBitvector(length, pI);
  }

  @Override
  public BitvectorFormula makeBitvector(int length, BigInteger pI) {
    return delegate.makeBitvector(length, pI);
  }

  @Override
  public BitvectorFormula makeBitvector(int length, IntegerFormula pI) {
    return delegate.makeBitvector(length, pI);
  }

  @Override
  public IntegerFormula toIntegerFormula(BitvectorFormula pI, boolean signed) {
    return delegate.toIntegerFormula(pI, signed);
  }

  @Override
  public BitvectorFormula makeVariable(int length, String pVar) {
    var term = delegate.makeVariable(length, pVar);
    symbolManager.addConstant(pVar, term);
    return term;
  }

  @Override
  public BitvectorFormula makeVariable(BitvectorType type, String pVar) {
    var term = delegate.makeVariable(type, pVar);
    symbolManager.addConstant(pVar, term);
    return term;
  }

  @Override
  public int getLength(BitvectorFormula number) {
    return delegate.getLength(number);
  }

  @Override
  public BitvectorFormula negate(BitvectorFormula number) {
    return delegate.negate(number);
  }

  @Override
  public BitvectorFormula add(BitvectorFormula number1, BitvectorFormula number2) {
    return delegate.add(number1, number2);
  }

  @Override
  public BitvectorFormula subtract(BitvectorFormula number1, BitvectorFormula number2) {
    return delegate.subtract(number1, number2);
  }

  @Override
  public BitvectorFormula divide(
      BitvectorFormula dividend, BitvectorFormula divisor, boolean signed) {
    return delegate.divide(dividend, divisor, signed);
  }

  @Override
  public BitvectorFormula smodulo(BitvectorFormula dividend, BitvectorFormula divisor) {
    return delegate.smodulo(dividend, divisor);
  }

  @Override
  public BitvectorFormula remainder(
      BitvectorFormula dividend, BitvectorFormula divisor, boolean signed) {
    return delegate.remainder(dividend, divisor, signed);
  }

  @Override
  public BitvectorFormula multiply(BitvectorFormula number1, BitvectorFormula number2) {
    return delegate.multiply(number1, number2);
  }

  @Override
  public BooleanFormula equal(BitvectorFormula number1, BitvectorFormula number2) {
    return delegate.equal(number1, number2);
  }

  @Override
  public BooleanFormula greaterThan(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    return delegate.greaterThan(number1, number2, signed);
  }

  @Override
  public BooleanFormula greaterOrEquals(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    return delegate.greaterOrEquals(number1, number2, signed);
  }

  @Override
  public BooleanFormula lessThan(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    return delegate.lessThan(number1, number2, signed);
  }

  @Override
  public BooleanFormula lessOrEquals(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    return delegate.lessOrEquals(number1, number2, signed);
  }

  @Override
  public BitvectorFormula not(BitvectorFormula bits) {
    return delegate.not(bits);
  }

  @Override
  public BitvectorFormula and(BitvectorFormula bits1, BitvectorFormula bits2) {
    return delegate.and(bits1, bits2);
  }

  @Override
  public BitvectorFormula or(BitvectorFormula bits1, BitvectorFormula bits2) {
    return delegate.or(bits1, bits2);
  }

  @Override
  public BitvectorFormula xor(BitvectorFormula bits1, BitvectorFormula bits2) {
    return delegate.xor(bits1, bits2);
  }

  @Override
  public BitvectorFormula shiftRight(
      BitvectorFormula number, BitvectorFormula toShift, boolean signed) {
    return delegate.shiftRight(number, toShift, signed);
  }

  @Override
  public BitvectorFormula shiftLeft(BitvectorFormula number, BitvectorFormula toShift) {
    return delegate.shiftLeft(number, toShift);
  }

  @Override
  public BitvectorFormula rotateLeft(BitvectorFormula number, int toRotate) {
    return delegate.rotateLeft(number, toRotate);
  }

  @Override
  public BitvectorFormula rotateLeft(BitvectorFormula number, BitvectorFormula toRotate) {
    return delegate.rotateLeft(number, toRotate);
  }

  @Override
  public BitvectorFormula rotateRight(BitvectorFormula number, int toRotate) {
    return delegate.rotateRight(number, toRotate);
  }

  @Override
  public BitvectorFormula rotateRight(BitvectorFormula number, BitvectorFormula toRotate) {
    return delegate.rotateRight(number, toRotate);
  }

  @Override
  public BitvectorFormula concat(BitvectorFormula prefix, BitvectorFormula suffix) {
    return delegate.concat(prefix, suffix);
  }

  @Override
  public BitvectorFormula extract(BitvectorFormula number, int msb, int lsb) {
    return delegate.extract(number, msb, lsb);
  }

  @Override
  public BitvectorFormula extend(BitvectorFormula number, int extensionBits, boolean signed) {
    return delegate.extend(number, extensionBits, signed);
  }

  @Override
  public BooleanFormula distinct(List<BitvectorFormula> pBits) {
    return delegate.distinct(pBits);
  }
}
