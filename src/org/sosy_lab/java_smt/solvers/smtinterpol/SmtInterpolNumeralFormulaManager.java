/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.smtinterpol;

import com.google.common.collect.Sets;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;

abstract class SmtInterpolNumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
        Term, Sort, SmtInterpolEnvironment, ParamFormulaType, ResultFormulaType, FunctionSymbol> {

  private static final Set<String> NUMERIC_FUNCTIONS =
      Sets.newHashSet("+", "-", "*", "/", "div", "mod");

  protected final SmtInterpolEnvironment env;
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

  /**
   * Check whether the current term is numeric and the value of a term is determined by only
   * numerals, i.e. no variable is contained.
   *
   * <p>Example: TRUE for "1", "2+3", "ite(x,2,3) and FALSE for "x", "x+2", "ite(1=2,x,0)"
   */
  boolean consistsOfNumerals(Term val) {
    Set<Term> finished = new HashSet<>();
    Deque<Term> waitlist = new ArrayDeque<>();
    waitlist.add(val);
    while (!waitlist.isEmpty()) {
      Term t = waitlist.pop();
      if (!finished.add(t)) {
        continue;
      }
      if (creator.isNumber(t)) {
        // true, skip and check others
      } else if (t instanceof ApplicationTerm) {
        final ApplicationTerm app = (ApplicationTerm) t;
        final FunctionSymbol func = app.getFunction();
        final Term[] params = app.getParameters();

        if (params.length == 0) {
          return false;
        } else if (NUMERIC_FUNCTIONS.contains(func.getName())) {
          for (Term param : params) {
            waitlist.add(param);
          }
        } else if ("ite".equals(func.getName())) {
          waitlist.add(params[2]);
        }
      } else {
        return false;
      }
    }
    return true;
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
    if (consistsOfNumerals(pNumber1) || consistsOfNumerals(pNumber2)) {
      return env.term("*", pNumber1, pNumber2);
    } else {
      return super.multiply(pNumber1, pNumber2);
    }
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
