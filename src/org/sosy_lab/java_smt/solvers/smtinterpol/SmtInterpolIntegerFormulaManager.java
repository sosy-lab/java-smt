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
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

class SmtInterpolIntegerFormulaManager
    extends SmtInterpolNumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {

  SmtInterpolIntegerFormulaManager(
      SmtInterpolFormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected Term makeNumberImpl(long i) {
    return getFormulaCreator().getEnv().numeral(BigInteger.valueOf(i));
  }

  @Override
  protected Term makeNumberImpl(BigInteger pI) {
    return getFormulaCreator().getEnv().numeral(pI);
  }

  @Override
  protected Term makeNumberImpl(String pI) {
    return getFormulaCreator().getEnv().numeral(pI);
  }

  @Override
  protected Term makeNumberImpl(double pNumber) {
    return makeNumberImpl((long) pNumber);
  }

  @Override
  protected Term makeNumberImpl(BigDecimal pNumber) {
    return decimalAsInteger(pNumber);
  }

  @Override
  protected Term makeVariableImpl(String varName) {
    Sort t = getFormulaCreator().getIntegerType();
    return getFormulaCreator().makeVariable(t, varName);
  }

  @Override
  public Term divide(Term pNumber1, Term pNumber2) {
    if (consistsOfNumerals(pNumber2)) {
      Sort intSort = pNumber1.getTheory().getNumericSort();
      assert intSort.equals(pNumber1.getSort()) && intSort.equals(pNumber2.getSort());
      return getFormulaCreator().getEnv().term("div", pNumber1, pNumber2);
    } else {
      return super.divide(pNumber1, pNumber2);
    }
  }

  @Override
  protected Term modulo(Term pNumber1, Term pNumber2) {
    if (consistsOfNumerals(pNumber2)) {
      Sort intSort = pNumber1.getTheory().getNumericSort();
      assert intSort.equals(pNumber1.getSort()) && intSort.equals(pNumber2.getSort());
      return getFormulaCreator().getEnv().term("mod", pNumber1, pNumber2);
    } else {
      return super.modulo(pNumber1, pNumber2);
    }
  }

  @Override
  protected Term modularCongruence(Term pNumber1, Term pNumber2, BigInteger pModulo) {
    return modularCongruence0(pNumber1, pNumber2, env.numeral(pModulo));
  }

  @Override
  protected Term modularCongruence(Term pNumber1, Term pNumber2, long pModulo) {
    return modularCongruence0(pNumber1, pNumber2, env.numeral(BigInteger.valueOf(pModulo)));
  }

  protected Term modularCongruence0(Term pNumber1, Term pNumber2, Term n) {
    Sort intSort = pNumber1.getTheory().getNumericSort();
    assert intSort.equals(pNumber1.getSort()) && intSort.equals(pNumber2.getSort());

    // ((_ divisible n) x)   <==>   (= x (* n (div x n)))
    Term x = subtract(pNumber1, pNumber2);
    return env.term("=", x, env.term("*", n, env.term("div", x, n)));
  }
}
