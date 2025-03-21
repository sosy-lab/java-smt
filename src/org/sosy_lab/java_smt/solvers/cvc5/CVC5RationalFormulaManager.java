// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.collect.FluentIterable;
import io.github.cvc5.Kind;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import java.math.BigDecimal;
import java.util.List;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;

public class CVC5RationalFormulaManager
    extends CVC5NumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {

  CVC5RationalFormulaManager(
      CVC5FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected Sort getNumeralType() {
    return getFormulaCreator().getRationalType();
  }

  @Override
  protected Term makeNumberImpl(double pNumber) {
    return makeNumberImpl(Double.toString(pNumber));
  }

  @Override
  protected Term makeNumberImpl(BigDecimal pNumber) {
    return makeNumberImpl(pNumber.toPlainString());
  }

  /** Make sure the value is real and add a cast if necessary */
  private Term toReal(Term pNumber) {
    return pNumber.getSort().isInteger() ? solver.mkTerm(Kind.TO_REAL, pNumber) : pNumber;
  }

  @Override
  public Term negate(Term number) {
    return super.negate(toReal(number));
  }

  @Override
  public Term add(Term number1, Term number2) {
    return super.add(toReal(number1), toReal(number2));
  }

  @Override
  protected Term sumImpl(List<Term> operands) {
    List<Term> castOperands = FluentIterable.from(operands).transform(this::toReal).toList();
    return super.sumImpl(castOperands);
  }

  @Override
  public Term subtract(Term number1, Term number2) {
    return super.subtract(toReal(number1), toReal(number2));
  }

  @Override
  public Term divide(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.DIVISION, pParam1, pParam2);
  }

  @Override
  public Term multiply(Term number1, Term number2) {
    return super.multiply(toReal(number1), toReal(number2));
  }

  @Override
  public Term equal(Term number1, Term number2) {
    return super.equal(toReal(number1), toReal(number2));
  }

  @Override
  protected Term distinctImpl(List<Term> operands) {
    List<Term> castOperands = FluentIterable.from(operands).transform(this::toReal).toList();
    return super.distinctImpl(castOperands);
  }

  @Override
  protected Term greaterThan(Term number1, Term number2) {
    return super.greaterThan(toReal(number1), toReal(number2));
  }

  @Override
  protected Term greaterOrEquals(Term number1, Term number2) {
    return super.greaterOrEquals(toReal(number1), toReal(number2));
  }

  @Override
  protected Term lessThan(Term number1, Term number2) {
    return super.lessThan(toReal(number1), toReal(number2));
  }

  @Override
  protected Term lessOrEquals(Term number1, Term number2) {
    return super.lessOrEquals(toReal(number1), toReal(number2));
  }

  @Override
  protected Term floor(Term pNumber) {
    return solver.mkTerm(Kind.TO_INTEGER, pNumber);
  }
}
