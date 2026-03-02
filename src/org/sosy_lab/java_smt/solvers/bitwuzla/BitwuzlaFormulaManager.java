// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Table;
import com.google.common.collect.Table.Cell;
import java.util.Collection;
import java.util.List;
import org.sosy_lab.common.collect.Collections3;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;
import org.sosy_lab.java_smt.basicimpl.Tokenizer;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Bitwuzla;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Kind;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Map_TermTerm;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Options;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Parser;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Sort;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.TermManager;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Vector_Int;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Vector_Term;

public final class BitwuzlaFormulaManager
    extends AbstractFormulaManager<Term, Sort, TermManager, BitwuzlaDeclaration> {
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
  public Term equalImpl(Iterable<Term> pArgs) {
    Vector_Term array = new Vector_Term(pArgs);
    if (array.size() < 2) {
      return creator.getEnv().mk_true();
    } else {
      return creator.getEnv().mk_term(Kind.EQUAL, array, new Vector_Int());
    }
  }

  @Override
  public Term distinctImpl(Iterable<Term> pArgs) {
    Vector_Term array = new Vector_Term(pArgs);
    if (array.size() < 2) {
      return creator.getEnv().mk_true();
    } else {
      return creator.getEnv().mk_term(Kind.DISTINCT, array, new Vector_Int());
    }
  }

  @Override
  protected List<Term> parseAllImpl(String formulaStr) throws IllegalArgumentException {
    // Split the input string into a list of SMT-LIB2 commands
    List<String> tokens = Tokenizer.tokenize(formulaStr);

    Table<String, Sort, Term> cache = creator.getCache();

    Collection<String> assertionCommands =
        tokens.stream().filter(Tokenizer::isAssertToken).collect(ImmutableList.toImmutableList());
    if (assertionCommands.isEmpty()) {
      return ImmutableList.of();
    }

    // Process the declarations
    Collection<String> declarationsFromTokens = getDeclarationsFromTokens(tokens, cache);

    // Build SMT-LIB2 declarations for all variables in the cache
    Collection<String> declarationFromCache = getDeclaredSymbolsFromCache(cache);

    String declsFromCache = String.join("\n", declarationFromCache);
    String declsFromTokens = String.join("\n", declarationsFromTokens);
    String assertionsFromTokens = String.join("\n", assertionCommands);

    // Add the declarations to the input and parse everything
    Parser parser = new Parser(creator.getEnv(), bitwuzlaOption);
    try {
      parser.parse(declsFromCache + declsFromTokens + assertionsFromTokens, true, false);
    } catch (IllegalArgumentException e) {
      throw new IllegalArgumentException(
          String.format(
              "Failed to parse input string \"%s\" with declarations \"%s\" and \"%s\"",
              assertionsFromTokens, declsFromCache, declsFromTokens),
          e);
    }

    // After the run, get the final assertion from the parser
    Vector_Term assertions = parser.bitwuzla().get_assertions();
    Preconditions.checkArgument(
        !assertions.isEmpty(), "No assertion found in input string \"%s\"", formulaStr);

    // Now get all symbols that were declared in the input
    Vector_Term declared = parser.get_declared_funs();

    List<Term> result =
        Collections3.transformedImmutableListCopy(
            assertions, assertion -> synchronizeSymbolsWithCache(declared, cache, assertion));

    // Return the updated term
    return result;
  }

  /**
   * Collect all new symbols from the parser and synchronize them with the variable cache. Finally,
   * substitute all symbols from the assertion with their original terms from the cache to be
   * consistent with previously created formulas.
   *
   * @return a term where all symbols are synchronized with the cache and can be used together with
   *     previously created formulas.
   */
  private Term synchronizeSymbolsWithCache(
      Vector_Term declared, Table<String, Sort, Term> cache, Term assertion) {
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
    return creator.getEnv().substitute_term(assertion, subst);
  }

  /** Return SMTLIB for all symbols from the cache, with one declaration per line. */
  private static Collection<String> getDeclaredSymbolsFromCache(Table<String, Sort, Term> cache) {
    ImmutableList.Builder<String> builder = ImmutableList.builder();
    for (Cell<String, Sort, Term> c : cache.cellSet()) {
      String symbol = c.getValue().toString();
      List<Sort> args = ImmutableList.of();
      Sort sort = c.getColumnKey();
      if (sort.is_fun()) {
        args = sort.fun_domain();
        sort = sort.fun_codomain();
      }
      String argsStr = Joiner.on(" ").join(args);
      builder.add(String.format("(declare-fun %s (%s) %s)", symbol, argsStr, sort));
    }
    return builder.build();
  }

  /**
   * Collect all declaration commands from the input tokens, parse them, and check if they are
   * consistent with the variable cache. If a declaration is consistent with the cache, skip it,
   * otherwise throw an exception.
   *
   * @return the list of all new-declaration non-assertion commands
   */
  private Collection<String> getDeclarationsFromTokens(
      List<String> tokens, Table<String, Sort, Term> cache) {
    ImmutableList.Builder<String> newDeclarations = ImmutableList.builder();
    for (String token : tokens) {
      if (Tokenizer.isAssertToken(token)) {
        // Skip assertions, they will be parsed at the end together with the declarations
        continue;
      } else if (Tokenizer.isDeclarationToken(token)) {
        // FIXME: Do we need to support function definitions here?
        Parser declParser = new Parser(creator.getEnv(), bitwuzlaOption);
        declParser.parse(token, true, false);
        Term parsed = declParser.get_declared_funs().get(0);

        String symbol = parsed.symbol();
        Sort sort = parsed.sort();

        // Check if the symbol is already defined in the variable cache
        if (cache.containsRow(symbol)) {
          if (!cache.contains(symbol, sort)) {
            // Sort of the definition that we parsed does not match the sort from the variable
            // cache.
            throw new IllegalArgumentException(
                String.format(
                    "Symbol %s is already defined with a different sort %s in the variable cache",
                    symbol, cache.row(symbol)));
          }
          // Skip if it's just a redefinition
          continue;
        }
      }
      // Otherwise, keep the command
      newDeclarations.add(token);
    }
    return newDeclarations.build();
  }

  @Override
  public String dumpFormulaImpl(Term pTerm) {
    // There are 2 ways of SMT2 printing in Bitwuzla, bitwuzla_term_print() and
    // bitwuzla_term_print_fmt(), which print a single formula, and bitwuzla_print_formula(),
    // which prints the complete assertion stack of the bitwuzla instance given to the function.
    // Only bitwuzla_print_formula() gives us the proper SMT2 format, with (check-sat) etc.
    // Note: bitwuzla_print_formula() is wrapped in dump_assertions_smt2()
    if (pTerm.is_value()) {
      return "(assert " + pTerm + ")";
    }
    Bitwuzla bitwuzla = new Bitwuzla(creator.getEnv());
    for (Term t : creator.getConstraintsForTerm(pTerm)) {
      bitwuzla.assert_formula(t);
    }
    bitwuzla.assert_formula(pTerm);
    return bitwuzla.print_formula();
  }

  static Term getBitwuzlaTerm(Formula pT) {
    return ((BitwuzlaFormula) pT).getTerm();
  }

  @Override
  public Term simplify(Term t) {
    return new Bitwuzla(creator.getEnv()).simplify(t);
  }
}
