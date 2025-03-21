// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import com.google.common.collect.FluentIterable;
import com.microsoft.z3.Native;
import java.math.BigDecimal;
import java.util.List;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;

class Z3RationalFormulaManager extends Z3NumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {

  Z3RationalFormulaManager(Z3FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected long getNumeralType() {
    return getFormulaCreator().getRationalType();
  }

  @Override
  protected Long makeNumberImpl(double pNumber) {
    return makeNumberImpl(Double.toString(pNumber));
  }

  @Override
  protected Long makeNumberImpl(BigDecimal pNumber) {
    return makeNumberImpl(pNumber.toPlainString());
  }

  /** Make sure the value is real and add a cast if necessary */
  private long toReal(long pNumber) {
    if (Native.getSort(z3context, pNumber) == formulaCreator.getIntegerType()) {
      long castNumber = Native.mkInt2real(z3context, pNumber);
      Native.incRef(z3context, castNumber);
      return castNumber;
    } else {
      return pNumber;
    }
  }

  @Override
  public Long negate(Long number) {
    return super.negate(toReal(number));
  }

  @Override
  public Long add(Long number1, Long number2) {
    return super.add(toReal(number1), toReal(number2));
  }

  @Override
  protected Long sumImpl(List<Long> operands) {
    List<Long> castOperands = FluentIterable.from(operands).transform(this::toReal).toList();
    return super.sumImpl(castOperands);
  }

  @Override
  public Long subtract(Long number1, Long number2) {
    return super.subtract(toReal(number1), toReal(number2));
  }

  @Override
  public Long divide(Long number1, Long number2) {
    return super.divide(toReal(number1), toReal(number2));
  }

  @Override
  public Long multiply(Long number1, Long number2) {
    return super.multiply(toReal(number1), toReal(number2));
  }

  @Override
  public Long equal(Long number1, Long number2) {
    return super.equal(toReal(number1), toReal(number2));
  }

  @Override
  protected Long distinctImpl(List<Long> operands) {
    List<Long> castOperands = FluentIterable.from(operands).transform(this::toReal).toList();
    return super.distinctImpl(castOperands);
  }

  @Override
  protected Long greaterThan(Long number1, Long number2) {
    return super.greaterThan(toReal(number1), toReal(number2));
  }

  @Override
  protected Long greaterOrEquals(Long number1, Long number2) {
    return super.greaterOrEquals(toReal(number1), toReal(number2));
  }

  @Override
  protected Long lessThan(Long number1, Long number2) {
    return super.lessThan(toReal(number1), toReal(number2));
  }

  @Override
  protected Long lessOrEquals(Long number1, Long number2) {
    return super.lessOrEquals(toReal(number1), toReal(number2));
  }

  @Override
  protected Long floor(Long pNumber) {
    return Native.mkReal2int(z3context, pNumber);
  }
}
