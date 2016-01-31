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

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Collection;

import javax.annotation.Nullable;

/** Collection of utilities for working with SmtInterpol */
class SmtInterpolUtil {
  private SmtInterpolUtil() {}

  public static boolean isVariable(Term t) {
    // A variable is the same as an UIF without parameters
    return !isTrue(t)
        && !isFalse(t)
        && (t instanceof ApplicationTerm)
        && ((ApplicationTerm) t).getParameters().length == 0
        && ((ApplicationTerm) t).getFunction().getDefinition() == null;
  }

  public static boolean isUF(Term t) {
    if (!(t instanceof ApplicationTerm)) {
      return false;
    }
    ApplicationTerm applicationTerm = (ApplicationTerm) t;
    FunctionSymbol func = applicationTerm.getFunction();
    return applicationTerm.getParameters().length > 0 && !func.isIntern() && !func.isInterpreted();
  }

  /** check for ConstantTerm with Number or
   * ApplicationTerm with negative Number */
  public static boolean isNumber(Term t) {
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
          && isNumber(at.getParameters()[0])) {
        is = true;

        // ApplicationTerm with Division --> "(/ 1 5)"
      } else if ("/".equals(at.getFunction().getName())
          && (at.getParameters().length == 2)
          && isNumber(at.getParameters()[0])
          && isNumber(at.getParameters()[1])) {
        is = true;
      }
    }

    // TODO hex or binary data, string?
    return is;
  }

  /** converts a term to a number,
   * currently only Double is supported. */
  public static Number toNumber(Term t) {
    assert isNumber(t) : "term is not a number: " + t;

    // ConstantTerm with Number --> "123"
    if (t instanceof ConstantTerm) {
      Object value = ((ConstantTerm) t).getValue();
      if (value instanceof Number) {
        return (Number) value;
      } else if (value instanceof Rational) {
        Rational rat = (Rational) value;
        if (t.getSort().getName().equals("Int") && rat.isIntegral()) {
          return rat.numerator();
        }
        return org.sosy_lab.common.rationals.Rational.of(rat.numerator(), rat.denominator());
      }

      // ApplicationTerm with negative Number --> "-123"
    } else if (t instanceof ApplicationTerm) {
      ApplicationTerm at = (ApplicationTerm) t;

      if ("-".equals(at.getFunction().getName())) {
        Object value = toNumber(at.getParameters()[0]);
        if (value instanceof BigDecimal) {
          return ((BigDecimal) value).negate();
        } else if (value instanceof BigInteger) {
          return ((BigInteger) value).negate();
        } else if (value instanceof Long) {
          return -(Long) value;
        } else if (value instanceof Integer) {
          return -(Integer) value;
        } else if (value instanceof Double) {
          return -(Double) value;
        } else if (value instanceof Float) {
          return -(Float) value;
        } else if (value instanceof org.sosy_lab.common.rationals.Rational) {
          return ((org.sosy_lab.common.rationals.Rational) value).negate();
        }
      }
    }

    throw new NumberFormatException("unknown format of numeric term: " + t);
  }

  public static boolean isBoolean(Term t) {
    return t.getTheory().getBooleanSort() == t.getSort();
  }

  public static boolean isFunction(Term t, String name) {
    return (t instanceof ApplicationTerm)
        && name.equals(((ApplicationTerm) t).getFunction().getName());
  }

  public static int getArity(Term t) {
    if (t instanceof ApplicationTerm) {
      return ((ApplicationTerm) t).getParameters().length;
    } else {
      return 0;
    }
  }

  public static @Nullable Term getArg(Term t, int i) {
    if (t instanceof ApplicationTerm) {
      return ((ApplicationTerm) t).getParameters()[i];
    } else {
      return null;
    }
  }

  public static boolean isTrue(Term t) {
    return t.getTheory().mTrue == t;
  }

  public static boolean isFalse(Term t) {
    return t.getTheory().mFalse == t;
  }

  /** this function creates a new Term with the same function and new parameters. */
  public static Term replaceArgs(SmtInterpolEnvironment env, Term t, Term[] newParams) {
    if (t instanceof ApplicationTerm) {
      ApplicationTerm at = (ApplicationTerm) t;
      Term[] oldParams = at.getParameters();

      assert oldParams.length == newParams.length;
      for (int i = 0; i < newParams.length; i++) {
        assert oldParams[i].getSort() == newParams[i].getSort()
            : "Cannot replace " + oldParams[i] + " with " + newParams[i] + ".";
      }

      FunctionSymbol funcSymb = at.getFunction();
      return env.term(funcSymb.getName(), funcSymb.getIndices(), null, newParams);
    } else {
      // ConstantTerm:            numeral, nothing to replace
      // AnnotatedTerm, LetTerm:  should not happen here
      return t;
    }
  }

  static Term[] toTermArray(Collection<? extends Term> terms) {
    return terms.toArray(new Term[terms.size()]);
  }

  /** this function can be used to print a bigger term*/
  public static String prettyPrint(Term t) {
    StringBuilder str = new StringBuilder();
    prettyPrint(t, str, 0);
    return str.toString();
  }

  private static void prettyPrint(Term t, StringBuilder str, int n) {
    for (int i = 0; i < n; i++) {
      str.append("  ");
    }
    if (t instanceof ApplicationTerm) {
      ApplicationTerm at = (ApplicationTerm) t;
      String function = at.getFunction().getName();
      if ("and".equals(function) || "or".equals(function)) {
        str.append("(").append(function).append("\n");
        for (Term child : at.getParameters()) {
          prettyPrint(child, str, n + 1);
        }
        for (int i = 0; i < n; i++) {
          str.append("  ");
        }
        str.append(")\n");
      } else {
        str.append(t.toStringDirect()).append("\n");
      }
    } else {
      str.append(t.toStringDirect()).append("\n");
    }
  }
}
