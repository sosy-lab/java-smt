// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.CVC5ParserException;
import io.github.cvc5.Command;
import io.github.cvc5.InputParser;
import io.github.cvc5.Kind;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.SymbolManager;
import io.github.cvc5.Term;
import io.github.cvc5.TermManager;
import io.github.cvc5.modes.InputLanguage;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

class CVC5FormulaManager extends AbstractFormulaManager<Term, Sort, TermManager, Term> {

  private final CVC5FormulaCreator creator;
  private final SymbolManager symbolManager;

  private static final String INVOKE_SUCCESS = "success\n";
  private static final Pattern PARSING_UNDECLARED_SYMBOL_PATTERN =
      Pattern.compile("Symbol '(?<undeclaredSymbol>.*)' not declared as a variable");
  private static final String PARSER_ERROR_CVC5 = "Error when parsing using CVC5: ";

  @SuppressWarnings("checkstyle:parameternumber")
  CVC5FormulaManager(
      CVC5FormulaCreator pFormulaCreator,
      CVC5UFManager pFfmgr,
      CVC5BooleanFormulaManager pBfmgr,
      CVC5IntegerFormulaManager pIfmgr,
      CVC5RationalFormulaManager pRfmgr,
      CVC5BitvectorFormulaManager pBvfmgr,
      CVC5FloatingPointFormulaManager pFpfmgr,
      CVC5QuantifiedFormulaManager pQfmgr,
      CVC5ArrayFormulaManager pAfmgr,
      CVC5SLFormulaManager pSLfmgr,
      CVC5StringFormulaManager pStrmgr,
      CVC5EnumerationFormulaManager pEfmgr) {
    super(
        pFormulaCreator,
        pFfmgr,
        pBfmgr,
        pIfmgr,
        pRfmgr,
        pBvfmgr,
        pFpfmgr,
        pQfmgr,
        pAfmgr,
        pSLfmgr,
        pStrmgr,
        pEfmgr);
    creator = pFormulaCreator;
    symbolManager = new SymbolManager(creator.getEnv());
  }

  static Term getCVC5Term(Formula pT) {
    checkArgument(
        pT instanceof CVC5Formula,
        "Cannot get the CVC5 term of type " + pT.getClass().getSimpleName() + " in the Solver!");
    return ((CVC5Formula) pT).getTerm();
  }

  @Override
  public Term parseImpl(String smtQuery) throws IllegalArgumentException {
    final Solver parseSolver = new Solver(creator.getEnv());
    final InputParser parser = getParser(parseSolver);
    try {
      parseQuery(smtQuery, parser, parseSolver);
      return getAndRegisterParsedTerm(parseSolver.getAssertions());
    } finally {
      parser.deletePointer();
      parseSolver.deletePointer();
    }
  }

  @Override
  public String dumpFormulaImpl(Term f) {
    checkArgument(
        getFormulaCreator().getFormulaType(f) == FormulaType.BooleanType,
        "Only BooleanFormulas may be dumped");

    StringBuilder variablesAndUFsAsSMTLIB2 = getAllDeclaredVariablesAndUFsAsSMTLIB2(f);

    // Add the final assert after the declarations
    variablesAndUFsAsSMTLIB2.append("(assert ").append(f).append(')');
    return variablesAndUFsAsSMTLIB2.toString();
  }

  // Collect all actually parsed symbols as far as possible, then restart with cached
  // symbols included if needed (this way we can use the correct symbols from the input string
  // easily to not include them from the cache and reduce possible mistakes with symbols that
  // need to be included from the cache)
  private void parseQuery(String smtQuery, final InputParser parser, final Solver parseSolver) {
    boolean retryNeeded = true;
    while (retryNeeded) {
      parser.setStringInput(InputLanguage.SMT_LIB_2_6, smtQuery, "");
      try {
        executeAllCommandsFromQuery(parser, parseSolver);
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
  private void executeAllCommandsFromQuery(InputParser parser, Solver parseSolver)
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
      return null; // could not find symbol in cache
    }

    StringBuilder declaration =
        getSMTLIB2DeclarationsFor(ImmutableMap.of(undeclaredSymbol, knownTerm));
    // TODO: insert after options if options present?
    return declaration.append(smtQuery).toString();
  }

  private Term getAndRegisterParsedTerm(Term[] assertions) {

    // Register new terms in our caches and check for errors in declarations
    Map<Term, Term> substitutions = getSymbolSubstitutions();

    // Get the assertions out of the solver and re-substitute definitions outside of assertions
    Term parsedTerm = getAssertedTerm(assertions);

    // If the symbols used in the term were already declared before parsing, the term uses new
    // ones with the same name, so we need to substitute them!
    parsedTerm = resubstituteVariables(parsedTerm, substitutions);

    // Quantified formulas do not give us the bound variables in getDeclaredTerms() above.
    // Find them and register a free equivalent
    creator.registerBoundVariablesWithVisitor(parsedTerm);
    return parsedTerm;
  }

  /**
   * Builds the parser from the given {@link Solver} and the {@link SymbolManager} of this class.
   * The {@link SymbolManager} needs to be persistent to remember terms already parsed/created.
   */
  private InputParser getParser(Solver parseSolver) {
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
   * Get all declared symbols from the symbol manager after parsing and register them in the
   * function/variable caches of the formula creator. If a symbol is already present in the cache, a
   * substitution from the newly parsed term to the cached one is recorded and returned.
   */
  private Map<Term, Term> getSymbolSubstitutions() {

    // For named definitions like (=> (! (> x y) : named p1) (! (= x z) : named p2))
    // TODO: how to handle this in CVC5 in JavaSMT?
    checkState(symbolManager.getNamedTerms().isEmpty());

    final Map<Term, Term> substitutions = new java.util.LinkedHashMap<>();
    for (Term declTerm : symbolManager.getDeclaredTerms()) {
      // TODO checks ALL declared terms, not only current ones from the parsed input! Overhead?
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

  private StringBuilder getAllDeclaredVariablesAndUFsAsSMTLIB2(Term f) {
    // We use our own map (instead of calling plain "extractVariablesAndUFs" without a map),
    // and then apply "buildKeepingLast" due to UFs;
    // an UF might be applied multiple times. But the names and the types are consistent.
    ImmutableMap.Builder<String, Term> allKnownVarsAndUFsBuilder = ImmutableMap.builder();
    creator.extractVariablesAndUFs(f, true, allKnownVarsAndUFsBuilder::put);
    return getSMTLIB2DeclarationsFor(allKnownVarsAndUFsBuilder.buildKeepingLast());
  }

  /**
   * Returns the SMTLIB2 declarations for the input Map with key=symbol for the value=term, line by
   * line with one declaration per line, with a line-break at the end of all lines. The output order
   * will match the order of the input map.
   */
  private static StringBuilder getSMTLIB2DeclarationsFor(ImmutableMap<String, Term> varsAndUFs) {
    StringBuilder declarations = new StringBuilder();
    for (Entry<String, Term> entry : varsAndUFs.entrySet()) {
      String name = entry.getKey();
      Term varOrUf = entry.getValue();

      // add function parameters
      Iterable<Sort> childrenTypes;
      try {
        if (varOrUf.getKind() == Kind.APPLY_UF) {
          // Unpack the def of the UF to get to the declaration which has the types
          varOrUf = varOrUf.getChild(0);
        }
      } catch (CVC5ApiException apiEx) {
        // Does not happen anyway
        throw new IllegalArgumentException("CVC5 internal error: " + apiEx.getMessage(), apiEx);
      }

      Sort sort = varOrUf.getSort();
      Sort returnType = sort;
      if (sort.isFunction()) {
        childrenTypes = Arrays.asList(sort.getFunctionDomainSorts());
        returnType = sort.getFunctionCodomainSort();
      } else {
        childrenTypes = Iterables.transform(varOrUf, Term::getSort);
      }

      // escaping is stolen from SMTInterpol, lets hope this remains consistent
      String qName = PrintTerm.quoteIdentifier(name);
      String args = Joiner.on(" ").join(childrenTypes);
      declarations.append(String.format("(declare-fun %s (%s) %s)\n", qName, args, returnType));
    }
    return declarations;
  }

  @Override
  public <T extends Formula> T substitute(
      final T f, final Map<? extends Formula, ? extends Formula> fromToMapping) {
    Map<Term, Term> castedMap = new LinkedHashMap<>();
    fromToMapping.forEach((k, v) -> castedMap.put(extractInfo(k), extractInfo(v)));
    Term substitutedTerm = resubstituteVariables(extractInfo(f), castedMap);
    return getFormulaCreator().encapsulate(getFormulaType(f), substitutedTerm);
  }

  private Term resubstituteVariables(Term parsedTerm, Map<Term, Term> fromToMapping) {
    Term[] substituteFrom = new Term[fromToMapping.size()];
    Term[] substituteTo = new Term[fromToMapping.size()];
    int idx = 0;
    for (Map.Entry<Term, Term> entry : fromToMapping.entrySet()) {
      substituteFrom[idx] = entry.getKey();
      substituteTo[idx] = entry.getValue();
      idx++;
    }
    return parsedTerm.substitute(substituteFrom, substituteTo);
  }

  /**
   * Collects the asserted term from the array of assertions returned by CVC5 after parsing.
   * Additionally, re-substitutes definitions outside of assertions back into the asserted term.
   */
  private static Term getAssertedTerm(Term[] assertions) {
    checkArgument(
        assertions.length > 0,
        PARSER_ERROR_CVC5 + "no term found. Did the input query contain assertions?");

    // There is only one assertion at index 0 in the parser's assertions array
    Term parsedTerm = checkNotNull(assertions[0]);

    // Additional definitions are provided from index 1 to length-1 in reversed order
    for (int i = assertions.length - 1; i >= 1; i--) {
      final Term definition = checkNotNull(assertions[i]);
      checkState(
          definition.getKind() == Kind.EQUAL,
          PARSER_ERROR_CVC5 + "unexpected term '%s' with kind '%s'",
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
