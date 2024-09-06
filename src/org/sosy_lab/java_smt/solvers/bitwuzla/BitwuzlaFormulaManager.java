// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Table;
import com.google.common.collect.Table.Cell;
import java.io.IOException;
import java.util.List;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Bitwuzla;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Map_TermTerm;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Options;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Parser;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Sort;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Vector_Term;

public final class BitwuzlaFormulaManager
    extends AbstractFormulaManager<Term, Sort, Void, BitwuzlaDeclaration> {
  private final BitwuzlaFormulaCreator creator;
  private final Options bitwuzlaOption;

  @SuppressWarnings("checkstyle:parameternumber")
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
    creator = pFormulaCreator;
    bitwuzlaOption = pBitwuzlaOptions;
  }

  @Override
  public BooleanFormula parse(String formulaStr) throws IllegalArgumentException {
    // Strip the input string and remove everything but declarations and assertions
    String s = stripSMTLIB2String(formulaStr);

    // Split the input string into a list of SMT-LIB2 commands
    List<String> tokens = tokenize(s);

    Table<String, Sort, Term> cache = creator.getCache();

    // Process the declarations
    ImmutableList.Builder<String> processed = ImmutableList.builder();
    for (String token : tokens) {
      if (isDecl(token)) {
        Parser declParser = new Parser(creator.getTermManager(), bitwuzlaOption);
        declParser.parse(token, true, false);
        Term parsed = declParser.get_declared_funs().get(0);

        String symbol = parsed.symbol();
        if (symbol.startsWith("|") && symbol.endsWith("|")) {
          // Strip quotes from the name
          symbol = symbol.substring(1, symbol.length() - 1);
        }
        Sort sort = parsed.sort();

        // Check if the symbol is already defined in the variable cache
        if (cache.containsRow(symbol)) {
          if (!cache.contains(symbol, sort)) {
            // Sort of the definition that we parsed does not match the sort from the variable
            // cache.
            throw new IllegalArgumentException();
          }
          // Skip if it's just a redefinition
          continue;
        }
      }
      // Otherwise, keep the command
      processed.add(token);
    }

    // Build SMT-LIB2 declarations for all variables in the cache
    ImmutableList.Builder<String> builder = ImmutableList.builder();
    for (Cell<String, Sort, Term> c : cache.cellSet()) {
      String symbol = c.getValue().toString();
      List<Sort> args = ImmutableList.of();
      Sort sort = c.getColumnKey();
      if (sort.is_fun()) {
        args = sort.fun_domain();
        sort = sort.fun_codomain();
      }
      StringBuilder decl = new StringBuilder();
      decl.append("(declare-fun").append(" ");
      decl.append(symbol).append(" ");
      decl.append("(");
      for (Sort p : args) {
        decl.append(p).append(" ");
      }
      decl.append(")").append(" ");
      decl.append(sort);
      decl.append(")");

      builder.add(decl.toString());
    }
    String decls = String.join("\n", builder.build());
    String input = String.join("\n", processed.build());

    // Add the declarations to the input and parse everything
    Parser parser = new Parser(creator.getTermManager(), bitwuzlaOption);
    parser.parse(decls + input, true, false);

    // After the run, get the final assertion from the parser
    Vector_Term assertions = parser.bitwuzla().get_assertions();
    Preconditions.checkArgument(
        !assertions.isEmpty(), "No assertion found in input string \"%s\"", formulaStr);
    Term result = Iterables.getLast(assertions);

    // Now get all symbols that were declared in the input
    Vector_Term declared = parser.get_declared_funs();

    // Process the symbols from the parser
    Map_TermTerm subst = new Map_TermTerm();
    for (Term term : declared) {
      if (cache.containsRow(term.symbol())) {
        // Symbol is from the context: add the original term to the substitution map
        subst.put(term, cache.get(term.symbol(), term.sort()));
      } else {
        // Symbol is new, add it to the context
        cache.put(term.symbol(), term.sort(), term);
      }
    }

    // Substitute all symbols from the context with their original terms
    result = creator.getTermManager().substitute_term(result, subst);

    // Return the updated term
    return creator.encapsulateBoolean(result);
  }

  private String stripSMTLIB2String(String pFormulaStr) {
    String s = pFormulaStr;
    int setLogicIndex = s.indexOf("(set-logic ");
    if (setLogicIndex != -1) {
      int endLogicIndex = s.indexOf(')', setLogicIndex + 1);
      String s1 = s.substring(0, setLogicIndex);
      String s2 = s.substring(endLogicIndex + 1);
      s = s1 + s2;
    }
    if (s.contains("(check-sat)")) {
      s = s.replace("(check-sat)", "");
    }
    if (s.contains("(exit)")) {
      s = s.replace("(exit)", "");
    }
    return s;
  }

  @Override
  public Appender dumpFormula(Term pTerm) {
    // There are 2 ways of SMT2 printing in Bitwuzla, bitwuzla_term_print() and
    // bitwuzla_term_print_fmt(), which print a single formula, and bitwuzla_print_formula(),
    // which prints the complete assertion stack of the bitwuzla instance given to the function.
    // Only bitwuzla_print_formula() gives us the proper SMT2 format, with (check-sat) etc.
    // Note: bitwuzla_print_formula() is wrapped in dump_assertions_smt2()
    return new Appenders.AbstractAppender() {
      @Override
      public void appendTo(Appendable out) throws IOException {
        Bitwuzla bitwuzla = new Bitwuzla(creator.getTermManager());
        for (Term t : creator.getVariableCasts()) {
          bitwuzla.assert_formula(t);
        }
        bitwuzla.assert_formula(pTerm);
        String dump = bitwuzla.print_formula();
        if (dump.startsWith("(set-logic ")) {
          dump = dump.substring(1 + dump.indexOf(')'));
        }
        dump = dump.replace("(check-sat)", "");
        dump = dump.replace("(exit)", "");
        out.append(dump);
      }
    };
  }

  static Term getBitwuzlaTerm(Formula pT) {
    return ((BitwuzlaFormula) pT).getTerm();
  }

  // Split up a sequence of lisp expressions
  // f.ex "(define-const a Int)(assert (= a 0)" becomes ["(define-const a Int)", "(assert (= a 0))"]
  public static List<String> tokenize(String input) {
    ImmutableList.Builder<String> builder = ImmutableList.builder();
    int level = 0;
    StringBuilder read = new StringBuilder();
    boolean inComment = false;
    for (int i = 0; i < input.length(); i++) {
      char c = input.charAt(i);
      if (inComment) {
        if (c == '\n') {
          inComment = false;
        }
        continue;
      }
      if (c == ';') {
        // Comment
        inComment = true;
        continue;
      }
      if (level == 0) {
        if (!Character.isWhitespace(c)) {
          if (c == '(') {
            read.append("(");
            level++;
          } else {
            // All top-level expressions should have parentheses around them
            throw new IllegalArgumentException();
          }
        }
      } else {
        read.append(c);
        if (c == '(') {
          level++;
        }
        if (c == ')') {
          if (level == 1) {
            builder.add(read.toString());
            read = new StringBuilder();
          }
          level--;
        }
      }
    }
    if (level != 0) {
      // Missing closing parenthesis
      throw new IllegalArgumentException();
    }
    return builder.build();
  }

  // Check if the token is a function or variable declaration
  public static boolean isDecl(String token) {
    // TODO: How to handle function *definitions*? And are they supported by Bitwuzla?
    return token.matches("\\(\\s*(declare-const|declare-fun).*");
  }
}
