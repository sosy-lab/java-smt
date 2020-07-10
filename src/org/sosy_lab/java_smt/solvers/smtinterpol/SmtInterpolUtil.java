// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.smtinterpol;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/** Collection of utilities for working with SmtInterpol. */
final class SmtInterpolUtil {
  private SmtInterpolUtil() {}

  /** this function can be used to print a bigger term. */
  public static String prettyPrint(Term t) {
    StringBuilder str = new StringBuilder();
    prettyPrint(t, str, 0);
    return str.toString();
  }

  private static void prettyPrint(Term t, StringBuilder str, int n) {
    str.append("  ".repeat(n));
    if (t instanceof ApplicationTerm) {
      ApplicationTerm at = (ApplicationTerm) t;
      String function = at.getFunction().getName();
      if ("and".equals(function) || "or".equals(function)) {
        str.append('(').append(function).append('\n');
        for (Term child : at.getParameters()) {
          prettyPrint(child, str, n + 1);
        }
        str.append("  ".repeat(n));
        str.append(")\n");
      } else {
        str.append(t.toStringDirect()).append('\n');
      }
    } else {
      str.append(t.toStringDirect()).append('\n');
    }
  }
}
