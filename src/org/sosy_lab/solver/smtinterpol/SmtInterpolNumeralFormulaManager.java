/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.solver.smtinterpol;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

import org.sosy_lab.solver.api.NumeralFormula;
import org.sosy_lab.solver.basicimpl.AbstractNumeralFormulaManager;

import java.math.BigInteger;

abstract class SmtInterpolNumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
        Term, Sort, SmtInterpolEnvironment, ParamFormulaType, ResultFormulaType> {

  private final SmtInterpolEnvironment env;
  private final SmtInterpolFormulaCreator creator;

  SmtInterpolNumeralFormulaManager(SmtInterpolFormulaCreator pCreator) {
    super(pCreator);
    creator = pCreator;
    env = pCreator.getEnv();
  }

  @Override
  protected boolean isNumeral(Term val) {
    return creator.isNumber(val);
  }

  @Override
  public Term negate(Term pNumber) {
    return env.term("*", env.numeral("-1"), pNumber);
  }

  @Override
  public Term add(Term pNumber1, Term pNumber2) {
    return env.term("+", pNumber1, pNumber2);
  }

  @Override
  public Term subtract(Term pNumber1, Term pNumber2) {
    return env.term("-", pNumber1, pNumber2);
  }

  @Override
  public Term multiply(Term pNumber1, Term pNumber2) {
    if (isNumeral(pNumber1) || isNumeral(pNumber2)) {
      return env.term("*", pNumber1, pNumber2);
    } else {
      return super.multiply(pNumber1, pNumber2);
    }
  }

  @Override
  protected Term modularCongruence(Term pNumber1, Term pNumber2, long pModulo) {
    // if x >= 0: ((_ divisible n) x)   <==>   (= x (* n (div x n)))
    // if x <  0: ((_ divisible n) x)   <==>   (= x (* n (div x n)))
    Sort intSort = pNumber1.getTheory().getNumericSort();
    if (pModulo > 0 && intSort.equals(pNumber1.getSort()) && intSort.equals(pNumber2.getSort())) {
      Term n = env.numeral(BigInteger.valueOf(pModulo));
      Term x = subtract(pNumber1, pNumber2);
      return env.term("=", x, env.term("*", n, env.term("div", x, n)));
    }
    return env.getTheory().mTrue;
  }

  @Override
  public Term equal(Term pNumber1, Term pNumber2) {
    return env.term("=", pNumber1, pNumber2);
  }

  @Override
  public Term greaterThan(Term pNumber1, Term pNumber2) {
    return env.term(">", pNumber1, pNumber2);
  }

  @Override
  public Term greaterOrEquals(Term pNumber1, Term pNumber2) {
    return env.term(">=", pNumber1, pNumber2);
  }

  @Override
  public Term lessThan(Term pNumber1, Term pNumber2) {
    return env.term("<", pNumber1, pNumber2);
  }

  @Override
  public Term lessOrEquals(Term pNumber1, Term pNumber2) {
    return env.term("<=", pNumber1, pNumber2);
  }
}
