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
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

class TraceBitvectorFormulaManager implements BitvectorFormulaManager {
  private final BitvectorFormulaManager delegate;
  private final TraceLogger logger;

  TraceBitvectorFormulaManager(BitvectorFormulaManager pDelegate, TraceLogger pLogger) {
    delegate = pDelegate;
    logger = pLogger;
  }

  @Override
  public BitvectorFormula makeBitvector(int length, long pI) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "makeBitvector(%s, %sL)".formatted(length, pI),
        () -> delegate.makeBitvector(length, pI));
  }

  @Override
  public BitvectorFormula makeBitvector(int length, BigInteger pI) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "makeBitvector(%s, new BigInteger(\"%s\"))".formatted(length, pI),
        () -> delegate.makeBitvector(length, pI));
  }

  @Override
  public BitvectorFormula makeBitvector(int length, IntegerFormula pI) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "makeBitvector(%s, %s)".formatted(length, logger.toVariable(pI)),
        () -> delegate.makeBitvector(length, pI));
  }

  @Override
  public IntegerFormula toIntegerFormula(BitvectorFormula pI, boolean signed) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "toIntegerFormula(%s, %s)".formatted(logger.toVariable(pI), signed),
        () -> delegate.toIntegerFormula(pI, signed));
  }

  @Override
  public BitvectorFormula makeVariable(int length, String pVar) {
    return makeVariable(FormulaType.getBitvectorTypeWithSize(length), pVar);
  }

  @Override
  public BitvectorFormula makeVariable(BitvectorType type, String pVar) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "makeVariable(%s, %s)".formatted(logger.printFormulaType(type), logger.printString(pVar)),
        () -> delegate.makeVariable(type, pVar));
  }

  @Override
  public int getLength(BitvectorFormula number) {
    return logger.logDefDiscard(
        "mgr.getBitvectorFormulaManager()",
        "getLength(%s)".formatted(logger.toVariable(number)),
        () -> delegate.getLength(number));
  }

  @Override
  public BitvectorFormula negate(BitvectorFormula number) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "negate(%s)".formatted(logger.toVariable(number)),
        () -> delegate.negate(number));
  }

  @Override
  public BitvectorFormula add(BitvectorFormula number1, BitvectorFormula number2) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "add(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.add(number1, number2));
  }

  @Override
  public BitvectorFormula subtract(BitvectorFormula number1, BitvectorFormula number2) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "subtract(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.subtract(number1, number2));
  }

  @Override
  public BitvectorFormula divide(
      BitvectorFormula dividend, BitvectorFormula divisor, boolean signed) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "divide(%s, %s, %s)"
            .formatted(logger.toVariable(dividend), logger.toVariable(divisor), signed),
        () -> delegate.divide(dividend, divisor, signed));
  }

  @Override
  public BitvectorFormula smodulo(BitvectorFormula dividend, BitvectorFormula divisor) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "smodulo(%s, %s)".formatted(logger.toVariable(dividend), logger.toVariable(dividend)),
        () -> delegate.smodulo(dividend, divisor));
  }

  @Override
  public BitvectorFormula remainder(
      BitvectorFormula dividend, BitvectorFormula divisor, boolean signed) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "remainder(%s, %s, %s)"
            .formatted(logger.toVariable(dividend), logger.toVariable(divisor), signed),
        () -> delegate.remainder(dividend, divisor, signed));
  }

  @Override
  public BitvectorFormula multiply(BitvectorFormula number1, BitvectorFormula number2) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "multiply(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.multiply(number1, number2));
  }

  @Override
  public BooleanFormula equal(BitvectorFormula number1, BitvectorFormula number2) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "equal(%s, %s)".formatted(logger.toVariable(number1), logger.toVariable(number2)),
        () -> delegate.equal(number1, number2));
  }

  @Override
  public BooleanFormula greaterThan(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "greaterThan(%s, %s, %s)"
            .formatted(logger.toVariable(number1), logger.toVariable(number2), signed),
        () -> delegate.greaterThan(number1, number2, signed));
  }

  @Override
  public BooleanFormula greaterOrEquals(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "greaterOrEquals(%s, %s, %s)"
            .formatted(logger.toVariable(number1), logger.toVariable(number2), signed),
        () -> delegate.greaterOrEquals(number1, number2, signed));
  }

  @Override
  public BooleanFormula lessThan(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "lessThan(%s, %s, %s)"
            .formatted(logger.toVariable(number1), logger.toVariable(number2), signed),
        () -> delegate.lessThan(number1, number2, signed));
  }

  @Override
  public BooleanFormula lessOrEquals(
      BitvectorFormula number1, BitvectorFormula number2, boolean signed) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "lessOrEquals(%s, %s, %s)"
            .formatted(logger.toVariable(number1), logger.toVariable(number2), signed),
        () -> delegate.lessOrEquals(number1, number2, signed));
  }

  @Override
  public BitvectorFormula not(BitvectorFormula bits) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "not(%s)".formatted(logger.toVariable(bits)),
        () -> delegate.not(bits));
  }

  @Override
  public BitvectorFormula and(BitvectorFormula bits1, BitvectorFormula bits2) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "and(%s, %s)".formatted(logger.toVariable(bits1), logger.toVariable(bits2)),
        () -> delegate.and(bits1, bits2));
  }

  @Override
  public BitvectorFormula or(BitvectorFormula bits1, BitvectorFormula bits2) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "or(%s, %s)".formatted(logger.toVariable(bits1), logger.toVariable(bits2)),
        () -> delegate.or(bits1, bits2));
  }

  @Override
  public BitvectorFormula xor(BitvectorFormula bits1, BitvectorFormula bits2) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "xor(%s, %s)".formatted(logger.toVariable(bits1), logger.toVariable(bits2)),
        () -> delegate.xor(bits1, bits2));
  }

  @Override
  public BitvectorFormula shiftRight(
      BitvectorFormula number, BitvectorFormula toShift, boolean signed) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "shiftRight(%s, %s, %s)"
            .formatted(logger.toVariable(number), logger.toVariable(toShift), signed),
        () -> delegate.shiftRight(number, toShift, signed));
  }

  @Override
  public BitvectorFormula shiftLeft(BitvectorFormula number, BitvectorFormula toShift) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "shiftLeft(%s, %s)".formatted(logger.toVariable(number), logger.toVariable(toShift)),
        () -> delegate.shiftLeft(number, toShift));
  }

  @Override
  public BitvectorFormula rotateLeft(BitvectorFormula number, int toRotate) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "rotateLeft(%s, %s)".formatted(logger.toVariable(number), toRotate),
        () -> delegate.rotateLeft(number, toRotate));
  }

  @Override
  public BitvectorFormula rotateLeft(BitvectorFormula number, BitvectorFormula toRotate) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "rotateLeft(%s, %s)".formatted(logger.toVariable(number), logger.toVariable(toRotate)),
        () -> delegate.rotateLeft(number, toRotate));
  }

  @Override
  public BitvectorFormula rotateRight(BitvectorFormula number, int toRotate) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "rotateRight(%s, %s)".formatted(logger.toVariable(number), toRotate),
        () -> delegate.rotateRight(number, toRotate));
  }

  @Override
  public BitvectorFormula rotateRight(BitvectorFormula number, BitvectorFormula toRotate) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "rotateRight(%s, %s)".formatted(logger.toVariable(number), logger.toVariable(toRotate)),
        () -> delegate.rotateRight(number, toRotate));
  }

  @Override
  public BitvectorFormula concat(BitvectorFormula prefix, BitvectorFormula suffix) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "concat(%s, %s)".formatted(logger.toVariable(prefix), logger.toVariable(prefix)),
        () -> delegate.concat(prefix, suffix));
  }

  @Override
  public BitvectorFormula extract(BitvectorFormula number, int msb, int lsb) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "extract(%s, %s, %s)".formatted(logger.toVariable(number), msb, lsb),
        () -> delegate.extract(number, msb, lsb));
  }

  @Override
  public BitvectorFormula extend(BitvectorFormula number, int extensionBits, boolean signed) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "extend(%s, %s, %s)".formatted(logger.toVariable(number), extensionBits, signed),
        () -> delegate.extend(number, extensionBits, signed));
  }

  @Override
  public BooleanFormula distinct(List<BitvectorFormula> pBits) {
    return logger.logDef(
        "mgr.getBitvectorFormulaManager()",
        "distinct(ImmutableList.of(%s))".formatted(logger.toVariables(pBits)),
        () -> delegate.distinct(pBits));
  }
}
