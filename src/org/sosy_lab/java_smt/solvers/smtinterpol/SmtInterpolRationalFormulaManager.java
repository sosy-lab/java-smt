// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import java.math.BigDecimal;
import java.math.BigInteger;
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
    return getFormulaCreator().getEnv().decimal(BigDecimal.valueOf(i));
  }

  @Override
  protected Term makeNumberImpl(BigInteger pI) {
    return getFormulaCreator().getEnv().decimal(new BigDecimal(pI));
  }

  @Override
  protected Term makeNumberImpl(String pI) {
    return getFormulaCreator().getEnv().decimal(pI);
  }

  @Override
  protected Term makeNumberImpl(Rational pI) {
    return getFormulaCreator()
        .getEnv()
        .getTheory()
        .rational(
            de.uni_freiburg.informatik.ultimate.logic.Rational.valueOf(pI.getNum(), pI.getDen()),
            getFormulaCreator().getEnv().getTheory().getRealSort());
  }

  @Override
  protected Term makeNumberImpl(double pNumber) {
    return getFormulaCreator().getEnv().decimal(BigDecimal.valueOf(pNumber));
  }

  @Override
  protected Term makeNumberImpl(BigDecimal pNumber) {
    return getFormulaCreator().getEnv().decimal(pNumber);
  }

  @Override
  protected Term makeVariableImpl(String varName) {
    Sort t = getFormulaCreator().getRationalType();
    return getFormulaCreator().makeVariable(t, varName);
  }

  @Override
  public Term divide(Term pNumber1, Term pNumber2) {
    if (consistsOfNumerals(pNumber2)) {
      Sort intSort = pNumber1.getTheory().getNumericSort();
      Sort realSort = pNumber1.getTheory().getRealSort();
      assert intSort.equals(pNumber1.getSort()) || realSort.equals(pNumber1.getSort());
      assert intSort.equals(pNumber2.getSort()) || realSort.equals(pNumber2.getSort());
      return getFormulaCreator().getEnv().term("/", pNumber1, pNumber2);
    } else {
      return super.divide(pNumber1, pNumber2);
    }
  }

  @Override
  protected Term floor(Term pNumber) {
    return getFormulaCreator().getEnv().term("to_int", pNumber);
  }
}
