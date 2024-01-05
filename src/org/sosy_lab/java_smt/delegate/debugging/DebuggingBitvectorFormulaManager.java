// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import java.math.BigInteger;
import java.util.List;
import java.util.Set;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

public class DebuggingBitvectorFormulaManager extends FormulaChecks
    implements BitvectorFormulaManager {
  private final BitvectorFormulaManager delegate;

  public DebuggingBitvectorFormulaManager(
      BitvectorFormulaManager pDelegate, Set<Formula> pLocalFormulas) {
    super(pLocalFormulas);
    delegate = pDelegate;
  }

  @Override
  public BitvectorFormula makeBitvector(int length, long pI) {
    assertThreadLocal();
    BitvectorFormula result = delegate.makeBitvector(length, pI);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula makeBitvector(int length, BigInteger pI) {
    assertThreadLocal();
    BitvectorFormula result = delegate.makeBitvector(length, pI);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula makeBitvector(int length, IntegerFormula pI) {
    assertThreadLocal();
    BitvectorFormula result = delegate.makeBitvector(length, pI);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public IntegerFormula toIntegerFormula(BitvectorFormula pI, boolean signed) {
    assertThreadLocal();
    assertFormulaInContext(pI);
    IntegerFormula result = delegate.toIntegerFormula(pI, signed);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula makeVariable(int length, String pVar) {
    assertThreadLocal();
    BitvectorFormula result = delegate.makeVariable(length, pVar);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula makeVariable(BitvectorType type, String pVar) {
    assertThreadLocal();
    BitvectorFormula result = delegate.makeVariable(type, pVar);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public int getLength(BitvectorFormula number) {
    assertThreadLocal();
    assertFormulaInContext(number);
    return delegate.getLength(number);
  }

  @Override
  public BitvectorFormula negate(BitvectorFormula number) {
    assertThreadLocal();
    assertFormulaInContext(number);
    BitvectorFormula result = delegate.negate(number);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula add(BitvectorFormula number1, BitvectorFormula number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BitvectorFormula result = delegate.add(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula subtract(BitvectorFormula number1, BitvectorFormula number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BitvectorFormula result = delegate.subtract(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula divide(
      BitvectorFormula numerator, BitvectorFormula denumerator, boolean signed) {
    assertThreadLocal();
    assertFormulaInContext(numerator);
    assertFormulaInContext(denumerator);
    BitvectorFormula result = delegate.divide(numerator, denumerator, signed);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula modulo(
      BitvectorFormula numerator, BitvectorFormula denumerator, boolean signed) {
    assertThreadLocal();
    assertFormulaInContext(numerator);
    assertFormulaInContext(denumerator);
    BitvectorFormula result = delegate.modulo(numerator, denumerator, signed);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula multiply(BitvectorFormula number1, BitvectorFormula number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BitvectorFormula result = delegate.multiply(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula equal(BitvectorFormula number1, BitvectorFormula number2) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BooleanFormula result = delegate.equal(number1, number2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula greaterThan(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BooleanFormula result = delegate.greaterThan(number1, number2, signed);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula greaterOrEquals(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {

    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BooleanFormula result = delegate.greaterOrEquals(number1, number2, signed);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula lessThan(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BooleanFormula result = delegate.lessThan(number1, number2, signed);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula lessOrEquals(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    assertThreadLocal();
    assertFormulaInContext(number1);
    assertFormulaInContext(number2);
    BooleanFormula result = delegate.lessOrEquals(number1, number2, signed);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula not(BitvectorFormula bits) {
    assertThreadLocal();
    assertFormulaInContext(bits);
    BitvectorFormula result = delegate.not(bits);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula and(BitvectorFormula bits1, BitvectorFormula bits2) {
    assertThreadLocal();
    assertFormulaInContext(bits1);
    assertFormulaInContext(bits2);
    BitvectorFormula result = delegate.and(bits1, bits2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula or(BitvectorFormula bits1, BitvectorFormula bits2) {
    assertThreadLocal();
    assertFormulaInContext(bits1);
    assertFormulaInContext(bits2);
    BitvectorFormula result = delegate.or(bits1, bits2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula xor(BitvectorFormula bits1, BitvectorFormula bits2) {
    assertThreadLocal();
    assertFormulaInContext(bits1);
    assertFormulaInContext(bits2);
    BitvectorFormula result = delegate.xor(bits1, bits2);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula shiftRight(
      BitvectorFormula number, BitvectorFormula toShift, boolean signed) {
    assertThreadLocal();
    assertFormulaInContext(number);
    assertFormulaInContext(toShift);
    BitvectorFormula result = delegate.shiftRight(number, toShift, signed);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula shiftLeft(BitvectorFormula number, BitvectorFormula toShift) {
    assertThreadLocal();
    assertFormulaInContext(number);
    assertFormulaInContext(toShift);
    BitvectorFormula result = delegate.shiftLeft(number, toShift);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula concat(BitvectorFormula prefix, BitvectorFormula suffix) {
    assertThreadLocal();
    assertFormulaInContext(prefix);
    assertFormulaInContext(suffix);
    BitvectorFormula result = delegate.concat(prefix, suffix);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula extract(BitvectorFormula number, int msb, int lsb) {
    assertThreadLocal();
    assertFormulaInContext(number);
    BitvectorFormula result = delegate.extract(number, msb, lsb);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BitvectorFormula extend(BitvectorFormula number, int extensionBits, boolean signed) {
    assertThreadLocal();
    assertFormulaInContext(number);
    BitvectorFormula result = delegate.extend(number, extensionBits, signed);
    addFormulaToContext(result);
    return result;
  }

  @Override
  public BooleanFormula distinct(List<BitvectorFormula> pBits) {
    assertThreadLocal();
    for (BitvectorFormula t : pBits) {
      assertFormulaInContext(t);
    }
    BooleanFormula result = delegate.distinct(pBits);
    addFormulaToContext(result);
    return result;
  }
}
