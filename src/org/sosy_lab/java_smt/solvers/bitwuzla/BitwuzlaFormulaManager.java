// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import com.google.common.base.Preconditions;
import java.io.IOException;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

final class BitwuzlaFormulaManager
    extends AbstractFormulaManager<Long, Long, Long, BitwuzlaDeclaration> {

  BitwuzlaFormulaManager(
      BitwuzlaFormulaCreator pFormulaCreator,
      BitwuzlaUFManager pFunctionManager,
      BitwuzlaBooleanFormulaManager pBooleanManager,
      BitwuzlaBitvectorFormulaManager pBitvectorManager,
      BitwuzlaQuantifiedFormulaManager pQuantifierManager,
      BitwuzlaFloatingPointManager pFloatingPointManager,
      BitwuzlaArrayFormulaManager pArrayManager) {
    super(
        pFormulaCreator,
        pFunctionManager,
        pBooleanManager,
        null,
        null,
        pBitvectorManager,
        pFloatingPointManager,
        pQuantifierManager,
        pArrayManager,
        null,
        null,
        null);
  }

  @Override
  public BooleanFormula parse(String s) throws IllegalArgumentException {
    if (s.contains("(check-sat)")) {
      s = s.replace("(check-sat)", "");
    }
    if (s.contains("(exit)")) {
      s = s.replace("(exit)", "");
    }
    long[] terms = BitwuzlaJNI.parse(s);
    Preconditions.checkArgument(terms != null, "Could not parse input string \"%s\"", s);
    assert terms != null;
    // AND all the terms
    Long retForm;
    if (terms.length > 1) {
      retForm =
          BitwuzlaJNI.bitwuzla_mk_term(
              BitwuzlaKind.BITWUZLA_KIND_AND.swigValue(), terms.length, terms);
    } else {
      retForm = terms[0];
    }
    assert BitwuzlaJNI.bitwuzla_term_is_bool(retForm);
    return super.getFormulaCreator().encapsulateBoolean(retForm);
  }

  @Override
  public Appender dumpFormula(Long pTerm) {
    // There are 2 ways of SMT2 printing in Bitwuzla, bitwuzla_term_print() and
    // bitwuzla_term_print_fmt(), which print a single formula, and bitwuzla_print_formula(),
    // which prints the complete assertion stack of the bitwuzla instance given to the function.
    // Only bitwuzla_print_formula() gives us the proper SMT2 format, with (check-sat) etc.
    // Note: bitwuzla_print_formula() is wrapped in dump_assertions_smt2()
    return new Appenders.AbstractAppender() {
      @Override
      public void appendTo(Appendable out) throws IOException {
        long printCtx = getFormulaCreator().getEnv();
        BitwuzlaJNI.bitwuzla_push(printCtx, 1);
        BitwuzlaJNI.bitwuzla_assert(printCtx, pTerm);
        String dump = BitwuzlaJNI.dump_assertions_smt2(printCtx, 10);
        BitwuzlaJNI.bitwuzla_pop(printCtx, 1);
        // Bitwuzla prints (check-sat)\n(exit)\n in the end. We remove that.
        if (dump.contains("(check-sat)\n")) {
          dump = dump.replace("(check-sat)", "");
        }
        if (dump.contains("(exit)")) {
          dump = dump.replace("(exit)", "");
        }
        out.append(dump);
      }
    };
  }

  static long getBitwuzlaTerm(Formula pT) {
    return ((BitwuzlaFormula) pT).getTerm();
  }
}
