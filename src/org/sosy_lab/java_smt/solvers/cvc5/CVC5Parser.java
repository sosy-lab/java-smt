/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.cvc5;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.CVC5ParserException;
import io.github.cvc5.Command;
import io.github.cvc5.InputParser;
import io.github.cvc5.Kind;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.SymbolManager;
import io.github.cvc5.Term;
import io.github.cvc5.modes.InputLanguage;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

class CVC5Parser {

  private static final String INVOKE_SUCCESS = "success\n";
  private static final Pattern PARSING_UNDECLARED_SYMBOL_PATTERN =
      Pattern.compile("Symbol '(?<undeclaredSymbol>.*)' not declared as a variable");
  private static final String PARSER_ERROR_CVC5 = "Error when parsing using CVC5: ";

  private final CVC5FormulaCreator creator;
  private final CVC5FormulaManager formulaManager;

  CVC5Parser(CVC5FormulaCreator pCreator, CVC5FormulaManager pCVC5FormulaManager) {
    creator = checkNotNull(pCreator);
    formulaManager = checkNotNull(pCVC5FormulaManager);
  }

  Term parse(String pSmtQuery) {
    final SymbolManager symbolManager = new SymbolManager(creator.getEnv());
    final Solver parseSolver = new Solver(creator.getEnv());
    final InputParser parser = getParser(symbolManager, parseSolver);
    try {
      parseQuery(pSmtQuery, parser, symbolManager, parseSolver);
      return getAndRegisterParsedTerm(parseSolver, symbolManager);
    } finally {
      parser.deletePointer();
      parseSolver.deletePointer();
      symbolManager.deletePointer();
    }
  }

  /**
   * Builds the parser from the given {@link Solver} and the {@link SymbolManager} of this class.
   * The {@link SymbolManager} needs to be persistent to remember terms already parsed/created.
   */
  private InputParser getParser(SymbolManager symbolManager, Solver parseSolver) {
    if (!parseSolver.isLogicSet()) {
      try {
        parseSolver.setLogic("ALL");
      } catch (CVC5ApiException e) {
        // Should never happen in this configuration
        throw new AssertionError("Unexpected exception", e);
      }
    }
    // Expected success string due to option set is "success\n" (as sanity check when invoking
    // parsing commands, which might also return errors!)
    parseSolver.setOption("print-success", "true");

    // More tolerant of non-conforming inputs, default: default
    // Allows e.g. parsing of Mathsat output with . in front of the definition names.
    parseSolver.setOption("parsing-mode", "lenient");

    // Force all declarations and definitions to be global when parsing, default: false
    // I.e. remembers declarations and definitions and helps to re-use them when parsed before etc.
    parseSolver.setOption("global-declarations", "true");

    // Use API interface for fresh constants when parsing declarations and definitions, default:
    // true
    // Parser re-uses existing declarations and definitions.
    parseSolver.setOption("fresh-declarations", "false");

    // Allows overloading of terms and sorts if true, default: true
    // Technically we want this to happen. But disabling this allows us to do it with our cache
    // safely and get better error messaged.
    parseSolver.setOption("term-sort-overload", "false");

    return new InputParser(parseSolver, symbolManager);
  }

  /**
   * Parses the given SMTLIB2 query string using the provided parser, symbol manager, and solver. In
   * case of undeclared symbols, it attempts to recover by including their declarations from the
   * formula creator's caches and retries parsing until successful or unrecoverable error occurs.
   */
  private void parseQuery(
      String smtQuery,
      final InputParser parser,
      final SymbolManager symbolManager,
      final Solver parseSolver) {
    boolean retryNeeded = true;
    while (retryNeeded) {
      parser.setStringInput(InputLanguage.SMT_LIB_2_6, smtQuery, "");
      try {
        executeAllCommandsFromQuery(parser, symbolManager, parseSolver);
        retryNeeded = false; // Success!
      } catch (CVC5ParserException e) {
        smtQuery = attemptRecovery(smtQuery, e);
        // If attemptRecovery returns null, it means it couldn't find the symbol, so we rethrow
        if (smtQuery == null) {
          throw new IllegalArgumentException(PARSER_ERROR_CVC5 + e.getMessage(), e);
        }
      }
    }
  }

  /**
   * @throws CVC5ParserException if parsing fails for any reason, including undeclared symbols or
   *     invalid format.
   * @throws IllegalArgumentException if the parser returns an unexpected result.
   */
  private void executeAllCommandsFromQuery(
      InputParser parser, SymbolManager symbolManager, Solver parseSolver)
      throws CVC5ParserException {
    for (Command cmd = parser.nextCommand(); !cmd.isNull(); cmd = parser.nextCommand()) {
      String result = cmd.invoke(parseSolver, symbolManager);
      checkArgument(
          INVOKE_SUCCESS.equals(result),
          "%sUnexpected parser result: %s",
          PARSER_ERROR_CVC5,
          result);
    }
  }

  /**
   * Attempts to recover from a parsing exception by checking if it is due to an undeclared symbol.
   * If so, it updates the SMTLIB2 query to include the declaration of the undeclared symbol from
   * the formula creator's caches. If recovery is not possible, it returns null.
   */
  private String attemptRecovery(String currentQuery, CVC5ParserException e) {
    Matcher matcher = PARSING_UNDECLARED_SYMBOL_PATTERN.matcher(e.getMessage());
    if (matcher.find()) {
      String symbol = matcher.group("undeclaredSymbol");
      return updateSMTLIB2QueryForUnrecognizedSymbol(currentQuery, symbol);
    }
    return null;
  }

  private String updateSMTLIB2QueryForUnrecognizedSymbol(String smtQuery, String undeclaredSymbol) {
    Term knownTerm = creator.functionsCache.get(undeclaredSymbol);
    if (knownTerm == null) {
      Map<String, Term> variableRow = creator.variablesCache.row(undeclaredSymbol);
      if (variableRow.size() == 1) {
        knownTerm = Iterables.getOnlyElement(variableRow.values());
      }
    }

    if (knownTerm == null) {
      return null; // could not find symbol in any cache
    }

    StringBuilder declaration =
        formulaManager.getSMTLIB2DeclarationsFor(ImmutableMap.of(undeclaredSymbol, knownTerm));
    // TODO: insert after options if options present?
    return declaration.append(smtQuery).toString();
  }

  private Term getAndRegisterParsedTerm(Solver parseSolver, SymbolManager symbolManager) {

    // Register new terms in our caches and check for errors in declarations
    Map<Term, Term> substitutions =
        getSymbolSubstitutions(symbolManager.getNamedTerms(), symbolManager.getDeclaredTerms());

    // Get the assertions out of the solver and re-substitute definitions outside of assertions
    Term parsedTerm = getAssertedTerm(parseSolver.getAssertions());

    // If the symbols used in the term were already declared before parsing, the term uses new
    // ones with the same name, so we need to substitute them!
    parsedTerm = formulaManager.substitute(parsedTerm, substitutions);

    // Quantified formulas do not give us the bound variables in getDeclaredTerms() above.
    // Find them and register a free equivalent
    creator.registerBoundVariablesWithVisitor(parsedTerm);
    return parsedTerm;
  }

  /**
   * Get all declared symbols from the symbol manager after parsing and register them in the
   * function/variable caches of the formula creator. If a symbol is already present in the cache, a
   * substitution from the newly parsed term to the cached one is recorded and returned.
   */
  private Map<Term, Term> getSymbolSubstitutions(
      Map<Term, String> namedTerms, Term[] declaredTerms) {

    // For named definitions like (=> (! (> x y) : named p1) (! (= x z) : named p2))
    // TODO: how to handle this in CVC5 in JavaSMT?
    checkState(namedTerms.isEmpty());

    final Map<Term, Term> substitutions = new LinkedHashMap<>();
    for (Term declTerm : declaredTerms) {
      try {
        Term termToRegister = declTerm.getKind() == Kind.APPLY_UF ? declTerm.getChild(0) : declTerm;
        registerNewTermSymbols(termToRegister, substitutions);
      } catch (CVC5ApiException apiException) {
        throw new IllegalArgumentException(PARSER_ERROR_CVC5 + declTerm, apiException);
      }
    }
    return substitutions;
  }

  /**
   * Registers the given term declaration in the function/variable caches of the formula creator. If
   * a symbol is already present in the cache, a substitution from the newly parsed term to the
   * cached one is recorded in the given substitutions map.
   */
  private void registerNewTermSymbols(Term declaration, Map<Term, Term> substitutions) {
    final String parsedTermString = declaration.toString();
    final Sort parsedSort = declaration.getSort();
    final String parsedSortString = parsedSort.toString();

    final Term funCacheHit = creator.functionsCache.get(parsedTermString);
    final Map<String, Term> termRowHit = creator.variablesCache.row(parsedTermString);
    final Term termCacheHit = termRowHit.get(parsedSortString);

    checkArgument(
        funCacheHit == null || termCacheHit == null,
        PARSER_ERROR_CVC5 + "the term '%s' is parsed with the 2 distinct sorts '%s' and '%s'",
        declaration,
        parsedSort,
        (funCacheHit == null ? "<null>" : funCacheHit.getSort()));
    checkArgument(
        termRowHit.isEmpty() || termRowHit.containsKey(parsedSortString),
        PARSER_ERROR_CVC5 + "the term '%s' is parsed with the 2 distinct sorts '%s' and '%s'",
        declaration,
        parsedSort,
        termRowHit.keySet());

    if (parsedSort.isFunction()) { // UF
      if (funCacheHit == null) {
        creator.functionsCache.put(parsedTermString, declaration);
      } else {
        substitutions.put(declaration, funCacheHit);
      }
    } else { // Variable
      if (termCacheHit == null) {
        creator.variablesCache.put(parsedTermString, parsedSortString, declaration);
      } else {
        substitutions.put(declaration, termCacheHit);
      }
    }
  }

  /**
   * Collects the asserted term from the array of assertions returned by CVC5 after parsing.
   * Additionally, re-substitutes definitions outside of assertions back into the asserted term.
   */
  private static Term getAssertedTerm(Term[] assertions) {
    checkArgument(
        assertions.length > 0,
        "%sNo term found. Did the input query contain assertions?",
        PARSER_ERROR_CVC5);

    // There is only one assertion at index 0 in the parser's assertions array
    Term parsedTerm = checkNotNull(assertions[0]);

    // Additional definitions are provided from index 1 to length-1 in reversed order,
    // such that transitive substitutions can be applied correctly.
    for (int i = assertions.length - 1; i >= 1; i--) {
      final Term definition = checkNotNull(assertions[i]);
      checkArgument(
          definition.getKind() == Kind.EQUAL,
          "%sUnexpected term '%s' with kind '%s'",
          PARSER_ERROR_CVC5,
          definition,
          definition.getKind());
      try {
        parsedTerm = parsedTerm.substitute(definition.getChild(0), definition.getChild(1));
      } catch (CVC5ApiException apiException) {
        throw new IllegalArgumentException(
            PARSER_ERROR_CVC5 + apiException.getMessage(), apiException);
      }
    }
    return parsedTerm;
  }
}
