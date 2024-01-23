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
import java.nio.file.Files;
import java.nio.file.Path;
import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Options;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Parser;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Sort;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Vector_Term;

final class BitwuzlaFormulaManager
    extends AbstractFormulaManager<Term, Sort, Void, BitwuzlaDeclaration> {

  private final Options bitwuzlaOption;

  BitwuzlaFormulaManager(
      BitwuzlaFormulaCreator pFormulaCreator,
      BitwuzlaUFManager pFunctionManager,
      BitwuzlaBooleanFormulaManager pBooleanManager,
      BitwuzlaBitvectorFormulaManager pBitvectorManager,
      BitwuzlaQuantifiedFormulaManager pQuantifierManager,
      BitwuzlaFloatingPointManager pFloatingPointManager,
      BitwuzlaArrayFormulaManager pArrayManager,
      Options pBitwuzlaOptions) {
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

    bitwuzlaOption = pBitwuzlaOptions;
  }

  @Override
  public BooleanFormula parse(String s) throws IllegalArgumentException {
    if (s.contains("(check-sat)")) {
      s = s.replace("(check-sat)", "");
    }
    if (s.contains("(exit)")) {
      s = s.replace("(exit)", "");
    }

    // create a temporary file and dump the formulas to it in SMTLIB2 format
    Path file;
    try {
      file = Files.createTempFile("bitwuzla-", ".smt2");
      Files.writeString(file, s);
    } catch (IOException e) {
      throw new RuntimeException("Could not created temporary file for parsing", e);
    }

    // run the parser on the temporary file
    Parser parser = new Parser(bitwuzlaOption, file.toString());
    String error = parser.parse(true);

    Preconditions.checkArgument(error.isEmpty(), error);
    Vector_Term assertions = parser.bitwuzla().get_assertions();

    Preconditions.checkArgument(assertions.size() == 1, "Could not parse input string \"%s\"", s);
    return getFormulaCreator().encapsulateBoolean(assertions.get(0));
  }

  @Override
  public Appender dumpFormula(Term pTerm) {
    // TODO: We need to reimplement this
    /*
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
    */
    throw new UnsupportedOperationException();
  }

  static Term getBitwuzlaTerm(Formula pT) {
    return ((BitwuzlaFormula) pT).getTerm();
  }
}
