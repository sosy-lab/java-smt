// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import com.google.common.collect.FluentIterable;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;

class SmtInterpolRationalFormulaManager
    extends SmtInterpolNumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {

  SmtInterpolRationalFormulaManager(
      SmtInterpolFormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected Term makeNumberImpl(long i) {
    return env.decimal(BigDecimal.valueOf(i));
  }

  @Override
  protected Term makeNumberImpl(BigInteger pI) {
    return env.decimal(new BigDecimal(pI));
  }

  @Override
  protected Term makeNumberImpl(String pI) {
    return env.decimal(pI);
  }

  @Override
  protected Term makeNumberImpl(Rational pI) {
    return env.getTheory()
        .rational(
            de.uni_freiburg.informatik.ultimate.logic.Rational.valueOf(pI.getNum(), pI.getDen()),
            env.getTheory().getRealSort());
  }

  @Override
  protected Term makeNumberImpl(double pNumber) {
    return env.decimal(BigDecimal.valueOf(pNumber));
  }

  @Override
  protected Term makeNumberImpl(BigDecimal pNumber) {
    return env.decimal(pNumber);
  }

  @Override
  protected Term makeVariableImpl(String varName) {
    Sort t = getFormulaCreator().getRationalType();
    return getFormulaCreator().makeVariable(t, varName);
  }

  /** Make sure the value is real and add a cast if necessary */
  private Term toReal(Term pNumber) {
    Sort intSort = pNumber.getTheory().getNumericSort();
    return pNumber.getSort().equals(intSort) ? env.term("to_real", pNumber) : pNumber;
  }

  @Override
  public Term negate(Term pNumber) {
    return super.negate(toReal(pNumber));
  }

  @Override
  public Term add(Term pNumber1, Term pNumber2) {
    return super.add(toReal(pNumber1), toReal(pNumber2));
  }

  @Override
  public Term sumImpl(List<Term> pOperands) {
    List<Term> castOperands = FluentIterable.from(pOperands).transform(this::toReal).toList();
    return super.sumImpl(castOperands);
  }

  @Override
  public Term subtract(Term pNumber1, Term pNumber2) {
    return super.subtract(toReal(pNumber1), toReal(pNumber2));
  }

  @Override
  public Term multiply(Term pNumber1, Term pNumber2) {
    return super.multiply(toReal(pNumber1), toReal(pNumber2));
  }

  @Override
  public Term divide(Term pNumber1, Term pNumber2) {
    if (consistsOfNumerals(pNumber2)) {
      return env.term("/", toReal(pNumber1), toReal(pNumber2));
    } else {
      return super.divide(pNumber1, pNumber2);
    }
  }

  @Override
  public Term equal(Term pNumber1, Term pNumber2) {
    return super.equal(toReal(pNumber1), toReal(pNumber2));
  }

  @Override
  public Term distinctImpl(List<Term> pOperands) {
    List<Term> castOperands = FluentIterable.from(pOperands).transform(this::toReal).toList();
    return super.distinctImpl(castOperands);
  }

  @Override
  public Term greaterThan(Term pNumber1, Term pNumber2) {
    return super.greaterThan(toReal(pNumber1), toReal(pNumber2));
  }

  @Override
  public Term greaterOrEquals(Term pNumber1, Term pNumber2) {
    return super.greaterOrEquals(toReal(pNumber1), toReal(pNumber2));
  }

  @Override
  public Term lessThan(Term pNumber1, Term pNumber2) {
    return super.lessThan(toReal(pNumber1), toReal(pNumber2));
  }

  @Override
  public Term lessOrEquals(Term pNumber1, Term pNumber2) {
    return super.lessOrEquals(toReal(pNumber1), toReal(pNumber2));
  }

  @Override
  protected Term floor(Term pNumber) {
    return env.term("to_int", pNumber);
  }
}
