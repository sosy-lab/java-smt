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
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import io.github.cvc5.CVC5ApiException;
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
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

class CVC5FormulaManager extends AbstractFormulaManager<Term, Sort, TermManager, Term> {

  private final CVC5FormulaCreator creator;

  private static final String INVOKE_SUCCESS = "success\n";
  public static final String PARSING_MISSING_SYMBOL_START = "Symbol ";
  public static final String PARSING_MISSING_SYMBOL_END = " not declared as a variable";
  private SymbolManager symbolManager;

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
    if (pT instanceof CVC5Formula) {
      return ((CVC5Formula) pT).getTerm();
    }
    throw new IllegalArgumentException(
        "Cannot get the formula info of type " + pT.getClass().getSimpleName() + " in the Solver!");
  }

  @Override
  public Term parseImpl(String formulaStr) throws IllegalArgumentException {
    return parseCVC5(formulaStr);
  }

  @Override
  public String dumpFormulaImpl(Term f) {
    assert getFormulaCreator().getFormulaType(f) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";

    StringBuilder variablesAndUFsAsSMTLIB2 = getAllDeclaredVariablesAndUFsAsSMTLIB2(f);

    // Add the final assert after the declarations
    variablesAndUFsAsSMTLIB2.append("(assert ").append(f).append(')');
    return variablesAndUFsAsSMTLIB2.toString();
  }

  // Collect all actually parsed symbols as far as possible, then restart with cached
  // symbols included if needed (this way we can use the correct symbols from the input string
  // easily to not include them from the cache and reduce possible mistakes with symbols that
  // need to be included from the cache)
  private Term parseCVC5(final String formulaStr) {
    // checkState(definitionsInInput.isEmpty()); // TODO: remove or use
    final Solver parseSolver = new Solver(creator.getEnv());
    final InputParser parser = getParser(parseSolver);

    parser.setStringInput(InputLanguage.SMT_LIB_2_6, formulaStr, "");

    ImmutableSet.Builder<Term> substituteFromBuilder = ImmutableSet.builder();
    ImmutableSet.Builder<Term> substituteToBuilder = ImmutableSet.builder();

    // "Commands" represent 1 definition or assertion from the input string
    Command command;
    try {
      // throws CVC5ParserException for errors, which can only be caught with Exception
      command = parser.nextCommand();
      while (!command.isNull()) {
        // Note: push and pop are not handled as we disallow SMTLIB2 input including it!

        // This WILL read in asserts, and they are no longer available for getTerm(), but on the
        // solver as assertions
        String invokeReturn = invokeCommand(command, parseSolver, symbolManager);

        if (!invokeReturn.equals(INVOKE_SUCCESS)) {
          throw new IllegalArgumentException("Error when parsing using CVC5: " + invokeReturn);
        }

        command = parser.nextCommand();
      }
    } catch (Exception parseException) {
      // nextCommand(); throws CVC5ParserException for errors, which can only be caught with
      // Exception
      if (parseException instanceof IllegalArgumentException) {
        throw (IllegalArgumentException) parseException;
      }

      String message = parseException.getMessage();
      if (message.startsWith(PARSING_MISSING_SYMBOL_START)
          && message.endsWith(PARSING_MISSING_SYMBOL_END)) {
        // This case seems to happen only very rarely (maybe just boolean variables or assertions
        // with 1 symbol in them?)! CVC5 seems to recognize most declared symbols just fine.

        // Strip the error message until only the symbol is left
        String symbolNotDeclared = message.substring(8, message.length() - 28);

        Term knownTerm = creator.functionsCache.get(symbolNotDeclared);
        if (knownTerm == null) {
          Map<String, Term> variableRow = creator.variablesCache.row(symbolNotDeclared);
          if (variableRow.size() == 1) {
            knownTerm = variableRow.values().iterator().next();
            return parseWithAddedSymbol(formulaStr, symbolNotDeclared, knownTerm);
          }
        } else {
          return parseWithAddedSymbol(formulaStr, symbolNotDeclared, knownTerm);
        }
      }

      throw new IllegalArgumentException(
          "Error parsing with CVC5: " + parseException.getMessage(), parseException);
    }

    // Register new terms in our caches or throw for errors
    registerNewTermsInCache(symbolManager, substituteFromBuilder, substituteToBuilder);

    // For named definitions like (=> (! (> x y) : named p1) (! (= x z) : named p2))
    // TODO: how to handle this in CVC5 in JavaSMT?
    checkState(symbolManager.getNamedTerms().isEmpty());

    // Get the assertions out of the solver and re-substitute additional definitions outside of
    // assertions
    Term parsedTerm = getAssertedTerm(parseSolver);

    // If the symbols used in the term were already declared before parsing, the term uses new
    // ones with the same name, so we need to substitute them!
    parsedTerm =
        resubstituteCachedVariables(
            substituteFromBuilder.build(), substituteToBuilder.build(), parsedTerm);

    // Quantified formulas do not give us the bound variables in getDeclaredTerms() above.
    // Find them and register a free equivalent
    creator.registerBoundVariablesWithVisitor(parsedTerm);

    parser.deletePointer(); // Clean up parser
    parseSolver.deletePointer(); // Clean up parse solver
    return parsedTerm;
  }

  private Term parseWithAddedSymbol(String formulaStr, String symbolNotDeclared, Term knownTerm) {
    StringBuilder declaration =
        getSMTLIB2DeclarationsFor(ImmutableMap.of(symbolNotDeclared, knownTerm));
    // TODO: insert after options if options present?
    return parseCVC5(declaration.append(formulaStr).toString());
  }

  /**
   * Builds the parser from the given {@link Solver} and the {@link SymbolManager}. The {@link
   * SymbolManager} needs to be persistent to remember terms already parsed/created.
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
    // Expected success string due to option set: "success\n"
    parseSolver.setOption("print-success", "true");
    // more tolerant of non-conforming inputs, default: default
    parseSolver.setOption("parsing-mode", "lenient");
    // force all declarations and definitions to be global when parsing, default: false
    parseSolver.setOption("global-declarations", "true");
    // use API interface for fresh constants when parsing declarations and definitions, default:
    // true
    parseSolver.setOption("fresh-declarations", "false");
    // allows overloading of terms and sorts if true, default: true
    parseSolver.setOption("term-sort-overload", "false");

    InputParser parser = new InputParser(parseSolver, symbolManager);
    return parser;
  }

  private void registerNewTermsInCache(
      SymbolManager sm,
      ImmutableSet.Builder<Term> substituteFromBuilder,
      ImmutableSet.Builder<Term> substituteToBuilder) {
    for (Term parsedTerm : sm.getDeclaredTerms()) {
      Term termToRegister = parsedTerm;
      try {
        Kind kind = termToRegister.getKind();
        if (kind == Kind.APPLY_UF) {
          termToRegister = termToRegister.getChild(0);
        }

        String parsedTermString = termToRegister.toString();
        Sort parsedSort = termToRegister.getSort();
        String parsedSortString = parsedSort.toString();

        Term funCacheHit = creator.functionsCache.get(parsedTermString);
        Map<String, Term> termRowHit = creator.variablesCache.row(parsedTermString);
        Term termCacheHit = termRowHit.get(parsedSortString);

        if (funCacheHit != null && termCacheHit != null) {
          throw new IllegalArgumentException(
              "Error parsing with CVC5: the parsed term "
                  + parsedTermString
                  + " is parsed with the 2 distinct sorts "
                  + parsedSortString
                  + " and "
                  + funCacheHit.getSort());
        } else if (!termRowHit.isEmpty() && !termRowHit.containsKey(parsedSortString)) {
          throw new IllegalArgumentException(
              "Error parsing with CVC5: the parsed term "
                  + parsedTermString
                  + " is parsed with the 2 distinct sorts "
                  + parsedSortString
                  + " and "
                  + termRowHit.keySet());
        }

        if (parsedSort.isFunction()) {
          // UFs
          if (funCacheHit == null) {
            creator.functionsCache.put(parsedTermString, termToRegister);

          } else {
            substituteFromBuilder.add(termToRegister);
            substituteToBuilder.add(funCacheHit);
          }

        } else {
          if (termCacheHit == null) {
            creator.variablesCache.put(parsedTermString, parsedSortString, termToRegister);

          } else {
            substituteFromBuilder.add(termToRegister);
            substituteToBuilder.add(termCacheHit);
          }
        }
      } catch (CVC5ApiException apiException) {
        throw new IllegalArgumentException(
            "Error parsing the following term in CVC5: " + parsedTerm, apiException);
      }
    }
  }

  private StringBuilder getAllDeclaredVariablesAndUFsAsSMTLIB2(Term f) {
    ImmutableMap.Builder<String, Term> allKnownVarsAndUFsBuilder = ImmutableMap.builder();
    // Get all symbols relevant for the input term
    creator.extractVariablesAndUFs(f, true, allKnownVarsAndUFsBuilder::put);

    // buildKeepingLast due to UFs; 1 UF might be applied multiple times. But the names and the
    // types are consistent.
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
      StringBuilder line = new StringBuilder();

      // escaping is stolen from SMTInterpol, lets hope this remains consistent
      line.append("(declare-fun ").append(PrintTerm.quoteIdentifier(name)).append(" (");

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
      if (sort.isFunction()) {
        childrenTypes = Arrays.asList(sort.getFunctionDomainSorts());
      } else {
        childrenTypes = Iterables.transform(varOrUf, Term::getSort);
      }

      line.append(Joiner.on(" ").join(childrenTypes));

      // Return type
      String returnTypeString = sort.toString();
      if (sort.isFunction()) {
        returnTypeString = sort.getFunctionCodomainSort().toString();
      }
      line.append(") ").append(returnTypeString).append(")\n");
      declarations.append(line);
    }
    return declarations;
  }

  @Override
  public <T extends Formula> T substitute(
      final T f, final Map<? extends Formula, ? extends Formula> fromToMapping) {
    Term[] changeFrom = new Term[fromToMapping.size()];
    Term[] changeTo = new Term[fromToMapping.size()];
    int idx = 0;
    for (Map.Entry<? extends Formula, ? extends Formula> e : fromToMapping.entrySet()) {
      changeFrom[idx] = extractInfo(e.getKey());
      changeTo[idx] = extractInfo(e.getValue());
      idx++;
    }
    Term input = extractInfo(f);
    FormulaType<T> type = getFormulaType(f);
    return getFormulaCreator().encapsulate(type, input.substitute(changeFrom, changeTo));
  }

  private String invokeCommand(Command command, Solver parseSolver, SymbolManager sm) {
    try {
      // throws CVC5ParserException for errors
      return command.invoke(parseSolver, sm);
    } catch (Exception parseException) {
      throw new IllegalArgumentException(
          "Error parsing with CVC5 " + parseException.getMessage(), parseException);
    }
  }

  private static Term resubstituteCachedVariables(
      Set<Term> substituteFrom, Set<Term> substituteTo, Term parsedTerm) {
    checkState(substituteFrom.size() == substituteTo.size());
    assert substituteFrom.stream()
        .map(Term::toString)
        .allMatch(from -> substituteTo.stream().map(Term::toString).anyMatch(from::equals));
    parsedTerm =
        parsedTerm.substitute(
            substituteFrom.toArray(new Term[0]), substituteTo.toArray(new Term[0]));
    return parsedTerm;
  }

  // Assumes that there is only one assertion at index 0 in the parsers assertions array
  // Additional definitions are ordered from index 1 to length - 1 REVERSED!
  private static Term getAssertedTerm(Solver parseSolver) {
    Term[] assertions = parseSolver.getAssertions();

    checkArgument(
        assertions.length > 0,
        "Error when parsing using CVC5: no term found to return."
            + " Did the input string contain assertions?");
    Term parsedTerm = assertions[0];
    checkState(!checkNotNull(parsedTerm).isNull());

    if (assertions.length > 1) {
      // Sometimes terms are added as assertions without them being sources by an assertion, but
      // as function-def. We re-substitute these into the assertion.
      for (int i = assertions.length - 1; i >= 1; i--) {
        Term parsedDefinition = assertions[i];

        try {
          Kind kind = parsedDefinition.getKind();
          if (kind == Kind.EQUAL) {
            parsedTerm =
                parsedTerm.substitute(parsedDefinition.getChild(0), parsedDefinition.getChild(1));
          } else {
            throw new IllegalArgumentException(
                "Error when parsing using CVC5: re-substitution of function-definitions into "
                    + "assertions failed due to unexpected term "
                    + parsedDefinition
                    + " kind "
                    + parsedDefinition.getKind());
          }

        } catch (CVC5ApiException apiException) {
          // getKind() will not throw here, but getChild() might for unexpected input
          throw new IllegalArgumentException(
              "Error parsing in CVC5: " + apiException.getMessage(), apiException);
        }
      }
    }
    return parsedTerm;
  }
}
