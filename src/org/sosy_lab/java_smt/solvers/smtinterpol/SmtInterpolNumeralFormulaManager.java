// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import com.google.common.collect.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;

@SuppressWarnings("ClassTypeParameterName")
abstract class SmtInterpolNumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
        Term, Sort, Script, ParamFormulaType, ResultFormulaType, FunctionSymbol> {

  /** Operators for arithmetic functions that return a numeric value. */
  private static final ImmutableSet<String> NUMERIC_FUNCTIONS =
      ImmutableSet.of("+", "-", "*", "/", "div", "mod", "to_real");

  protected final Script env;

  SmtInterpolNumeralFormulaManager(
      SmtInterpolFormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
    env = pCreator.getEnv();
  }

  /** check for ConstantTerm with Number or ApplicationTerm with negative Number. */
  @Override
  protected final boolean isNumeral(Term t) {
    boolean is = false;
    // ConstantTerm with Number --> "123"
    if (t instanceof ConstantTerm) {
      Object value = ((ConstantTerm) t).getValue();
      if (value instanceof Number || value instanceof Rational) {
        is = true;
      }

    } else if (t instanceof ApplicationTerm) {
      ApplicationTerm at = (ApplicationTerm) t;

      // ApplicationTerm with negative Number --> "(- 123)"
      if ("-".equals(at.getFunction().getName())
          && (at.getParameters().length == 1)
          && isNumeral(at.getParameters()[0])) {
        is = true;

        // ApplicationTerm with Division --> "(/ 1 5)"
      } else if ("/".equals(at.getFunction().getName())
          && (at.getParameters().length == 2)
          && isNumeral(at.getParameters()[0])
          && isNumeral(at.getParameters()[1])) {
        is = true;
      }
    }

    // TODO hex or binary data, string?
    return is;
  }

  /**
   * Check whether the current term is numeric and the value of a term is determined by only
   * numerals, i.e. no variable is contained. This method should check as precisely as possible the
   * situations in which SMTInterpol supports arithmetic operations like multiplications.
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
      if (isNumeral(t)) {
        // true, skip and check others
      } else if (t instanceof ApplicationTerm) {
        final ApplicationTerm app = (ApplicationTerm) t;
        final FunctionSymbol func = app.getFunction();
        final Term[] params = app.getParameters();

        if (params.length == 0) {
          return false;
        } else if (NUMERIC_FUNCTIONS.contains(func.getName())) {
          waitlist.addAll(Arrays.asList(params));
        } else if ("ite".equals(func.getName())) {
          // ignore condition, just use the if- and then-case
          waitlist.add(params[1]);
          waitlist.add(params[2]);
        } else {
          return false;
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
  public Term distinctImpl(List<Term> pNumbers) {
    if (pNumbers.size() < 2) {
      return env.getTheory().mTrue;
    } else {
      return env.term("distinct", pNumbers.toArray(new Term[0]));
    }
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

  @Override
  public Term toRational(Term formula) {
    return env.term("to_real", formula);
  }
}
