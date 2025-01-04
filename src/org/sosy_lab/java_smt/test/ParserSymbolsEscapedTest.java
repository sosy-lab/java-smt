/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;
import static org.sosy_lab.java_smt.basicimpl.FormulaCreator.RESERVED;

import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.Collection;
import org.junit.Before;
import org.junit.Test;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class ParserSymbolsEscapedTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  public static ImmutableSet<String> TEST_SYMBOLS =
      ImmutableSet.of(
          // Simple symbols from the standard:
          "+",
          "<=",
          "x",
          "plus",
          "**",
          "$",
          "<sas",
          "<adf>",
          "abc77",
          "*$s&6",
          ".kkk",
          ".8",
          "+34",
          "-32",
          // Quoted symbols from the standard:
          "this is a quoted symbol",
          "so is\nthis one",
          "\" can occur too",
          "af klj ^*0 asfe2 (&*)&(#^ $ > > >?\" ’]]984",
          // Some more edge cases
          "",
          " ",
          "\n",
          "ꯍ",
          "#b101011",
          "#b2",
          "1",
          "01",
          "1.0",
          "01.0",
          "#xA04",
          "#xR04",
          "#o70");

  private static final ImmutableList<String> reserved =
      ImmutableList.of(
          // Reserved
          "_",
          "!",
          "as",
          "let",
          "exists",
          "forall",
          "match",
          "par",

          // Commands
          "assert",
          "check-sat",
          "check-sat-assuming",
          "declare-const",
          "declare-datatype",
          "declare-datatypes",
          "declare-fun",
          "declare-sort",
          "define-fun",
          "define-fun-rec",
          "define-funs-rec",
          "define-sort",
          "echo",
          "exit",
          "get-assertions",
          "get-assignment",
          "get-info",
          "get-model",
          "get-option",
          "get-proof",
          "get-unsat-assumptions",
          "get-unsat-core",
          "get-value",
          "pop",
          "push",
          "reset",
          "reset-assertions",
          "set-info",
          "set-logic",
          "set-option",

          // Predefined symbols
          // Array
          "select",
          "store",
          // Bitvector
          "concat",
          "extract",
          "bvnot",
          "bvneg",
          "bvand",
          "bvor",
          "bvadd",
          "bvmul",
          "bvudiv",
          "bvurem",
          "bvshl",
          "bvlshr",
          "true",
          "false",
          "not",
          "=>",
          "and",
          "or",
          "xor",
          "=",
          "distinct",
          "ite"
          // TODO: Add more theories
          );

  @Parameters(name = "{0},{1}")
  public static Collection<Object[]> data() {
    ImmutableSet.Builder<Object[]> builder = ImmutableSet.builder();
    for (Solvers solver : Solvers.values()) {
      for (String symbol :
          FluentIterable.concat(
              RESERVED,
              TEST_SYMBOLS,
              VariableNamesTest.NAMES,
              VariableNamesTest.UNSUPPORTED_NAMES)) {
        for (String variant :
            ImmutableSet.of(
                symbol,
                addQuotes(symbol),
                FormulaCreator.escapeName(symbol),
                addQuotes(FormulaCreator.escapeName(symbol)))) {
          builder.add(new Object[] {solver, variant});
        }
      }
    }
    return builder.build();
  }

  @Parameter(0)
  public Solvers solver;

  @Parameter(1)
  public String symbol;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Before
  public void init() {
    requireParser();
  }

  /** Is this <code>True</code> if the symbol is a reserved keyword in the SMTLIB standard. */
  private static boolean isReserved(String pSymbol) {
    return RESERVED.contains(pSymbol);
  }

  /** <code>True</code> if the symbol is a simple symbol according to the SMTLIB standard. */
  private static boolean isSimple(String pSymbol) {
    return pSymbol.matches("^[~!@$%^&*_\\-+=<>.?\\/0-9a-zA-Z]+$")
        && !Character.isDigit(pSymbol.charAt(0))
        && !isReserved(pSymbol);
  }

  /**
   * <code>True</code> if the symbol is a valid symbol according to the SMTLIB standard.
   *
   * <p>Valid symbols can be either <code>simple</code> symbols or <code>quoted</code> symbols.
   */
  private static boolean isValid(String pSymbol) {
    if (pSymbol.length() >= 2 && pSymbol.startsWith("|") && pSymbol.endsWith("|")) {
      return FormulaCreator.isValidName(removeQuotes(pSymbol));
    } else {
      return pSymbol.matches("^[~!@$%^&*_\\-+=<>.?\\/0-9a-zA-Z]+$")
          && FormulaCreator.isValidName(pSymbol);
    }
  }

  /**
   * Remove quotes from the symbol.
   *
   * <p>If the symbol is not quoted, return it unchanged.
   */
  private static String removeQuotes(String pSymbol) {
    if (pSymbol.length() >= 2 && pSymbol.startsWith("|") && pSymbol.endsWith("|")) {
      return pSymbol.substring(1, pSymbol.length() - 1);
    } else {
      return pSymbol;
    }
  }

  /**
   * Add quotes to the symbol
   *
   * <p>Assumes that the symbol is not already quoted.
   */
  private static String addQuotes(String pSymbol) {
    return "|" + pSymbol + "|";
  }

  private static boolean hasQuotes(String pSymbol) {
    return pSymbol.length() >= 2 && pSymbol.startsWith("|") && pSymbol.endsWith("|");
  }

  /**
   * Return the canonical representation of the symbol.
   *
   * <p>The symbol will have quotes if and only if the same symbol without quotes would not be legal
   * in SMTLIB.
   */
  private static String canonical(String pSymbol) {
    String noquotes = removeQuotes(pSymbol);
    return isSimple(noquotes) ? noquotes : addQuotes(noquotes);
  }

  /** Parse a variable definition in the SMTLIB format and return the term. */
  private BooleanFormula parseSymbol(String pSymbol, boolean asUfSymbol) {
    String sort = solver == Solvers.BITWUZLA ? "(_ BitVec 8)" : "Int";
    String query =
        asUfSymbol
            ? String.format(
                "(declare-const c %s)(declare-fun %s (%s) Bool)(assert (%s c))",
                sort, pSymbol, sort, pSymbol)
            : String.format("(declare-const %s Bool)(assert %s)", pSymbol, pSymbol);
    return mgr.parse(query);
  }

  private void forValidSymbols(String pSymbol) {
    assume().that(isValid(pSymbol)).isTrue();
  }

  private void forInvalidSymbols(String pSymbol) {
    assume().that(isValid(pSymbol)).isFalse();
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void testEscapedParserValid() {
    forValidSymbols(symbol);
    if (solver == Solvers.BITWUZLA) {
      // TODO Report as a bug
      assume().that(symbol).matches("^[~!@$%^&*_\\-+=<>.?\\/0-9a-zA-Z]+$");
    }
    parseSymbol(symbol, false);
  }

  @Test
  @SuppressWarnings("CheckReturnValue")
  public void testEscapedParserValidUf() {
    forValidSymbols(symbol);
    if (solver == Solvers.BITWUZLA) {
      // TODO Report as a bug
      assume().that(symbol).matches("^[~!@$%^&*_\\-+=<>.?\\/0-9a-zA-Z]+$");
    }
    parseSymbol(symbol, true);
  }

  @Test
  public void testEscapedParserInvalid() {
    forInvalidSymbols(symbol);
    if (solver == Solvers.OPENSMT) {
      // TODO Report as a bug
      if (!hasQuotes(symbol)) {
        assume().that(symbol).matches("^[~!@$%^&*_\\-+=<>.?\\/0-9a-zA-Z]+$");
      }
    }
    assertThrows(IllegalArgumentException.class, () -> parseSymbol(symbol, false));
  }

  @Test
  public void testEscapedVariableVisitor() {
    BooleanFormula f = mgr.getBooleanFormulaManager().makeVariable(symbol);
    ImmutableSet<String> variables = mgr.extractVariables(f).keySet();
    assertThat(variables).containsExactly(symbol);
  }

  @Test
  public void testEscapedDumpAndParse() {
    if (solver == Solvers.BITWUZLA) {
      // TODO This might already be fixed in another branch
      // FIXME Fix the exception handler so that Bitwuzla doesn't crash the JVM
      assume().that(symbol).matches("^[~!@$%^&*_\\-+=<>.?\\/0-9a-zA-Z]+$");
    }
    BooleanFormula f = mgr.getBooleanFormulaManager().makeVariable(symbol);
    BooleanFormula g = mgr.parse(mgr.dumpFormula(f).toString());
    assertThat(f).isEqualTo(g);
  }
}
