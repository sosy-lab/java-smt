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
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

class CVC5FormulaManager extends AbstractFormulaManager<Term, Sort, TermManager, Term> {

  private final CVC5FormulaCreator creator;

  private static final String INVOKE_SUCCESS = "success\n";

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
    TermManager env = creator.getEnv();
    Solver parseSolver = new Solver(env);
    SymbolManager sm = new SymbolManager(env);
    if (!parseSolver.isLogicSet()) {
      try {
        parseSolver.setLogic("ALL");
      } catch (CVC5ApiException e) {
        // Should never happen in this configuration
        throw new AssertionError("Unexpected exception", e);
      }
    }
    // Expected success string: "success\n"
    parseSolver.setOption("print-success", "true");
    InputParser parser = new InputParser(parseSolver, sm);

    // Add all already known (cached) variables and UFs
    // (double parsing is a problem for UFs it seems, and the internal UFs cause problems)
    String sanitizedInputFormula = addCachedDeclarationsTo(formulaStr);
    boolean mathsatReplacement = false;
    // Sanitize input String for CVC5 (it disallows . and @ without quotes)
    if (sanitizedInputFormula.contains("define-fun .def_")) {
      mathsatReplacement = true;
      sanitizedInputFormula = sanitizeInputForMathsat(sanitizedInputFormula);
    }

    parser.setStringInput(InputLanguage.SMT_LIB_2_6, sanitizedInputFormula, "");

    ImmutableSet.Builder<Term> substituteFromBuilder = ImmutableSet.builder();
    ImmutableSet.Builder<Term> substituteToBuilder = ImmutableSet.builder();

    int numberOfAssertions = 0;
    Command command = getNextCommand(parser);
    while (!command.isNull()) {
      if (command.toString().contains("push") || command.toString().contains("pop")) {
        // TODO: push and pop?
        throw new IllegalArgumentException(
            "Parsing SMTLIB2 with CVC5 in JavaSMT does not support push or pop currently.");
      }

      if (command.toString().startsWith("(assert ")) {
        numberOfAssertions++;
      }

      // This WILL read in asserts, and they are no longer available for getTerm(), but on the
      // solver as assertions
      String invokeReturn = invokeCommand(command, parseSolver, sm);

      if (!invokeReturn.equals(INVOKE_SUCCESS)) {
        throw new IllegalArgumentException("Error when parsing using CVC5: " + invokeReturn);
      }

      command = getNextCommand(parser);
    }

    // Register new terms in our caches or throw for errors
    registerNewTermsInCache(sm, substituteFromBuilder, substituteToBuilder);

    // For named definitions like (=> (! (> x y) : named p1) (! (= x z) : named p2))
    // TODO: how to handle this in CVC5 in JavaSMT?
    checkState(sm.getNamedTerms().isEmpty());

    // Get the assertions out of the solver and re-substitute additional definitions outside of
    // assertions
    Term parsedTerm = getAssertedTerm(parseSolver, numberOfAssertions, mathsatReplacement);

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

  private String addCachedDeclarationsTo(String formulaStr) {
    // Add all already known (cached) variables and UFs
    // (double parsing is a problem for UFs it seems, and the internal UFs cause problems)
    Set<String> declarationsForAllVarsAndUfs =
        getSMTLIB2DeclarationsFor(
            ImmutableMap.<String, Term>builder()
                .putAll(creator.getAllCachedVariablesAndUFs(true, true))
                .buildOrThrow());

    StringBuilder extraDefs = new StringBuilder();
    for (String declaration : declarationsForAllVarsAndUfs) {
      // Remove newline from the end
      String declWoNewline = declaration.substring(0, declaration.length() - 1);
      if (!formulaStr.contains(declWoNewline)) {
        if (!declWoNewline.contains("()")) {
          extraDefs.append(declaration);
        } else if (!formulaStr.contains(
            declWoNewline.replace("(declare-fun ", "(declare-const ").replace(" ()", ""))) {
          // No "input" value; may be a variable, which can be defined using declare-const as well
          extraDefs.append(declaration);
        }
      }
    }
    return extraDefs.append(formulaStr).toString();
  }

  private String sanitizeInputForMathsat(String inputString) {
    // MathSAT5 output, resubstitute the illegal input.
    // Since no quotes are used, we can assume that there are no spaces in the defined name.
    ImmutableMap.Builder<String, String> replacementMapBuilder = ImmutableMap.builder();
    String sanitizedInputFormula = inputString;
    String pattern = "(define-fun \\.)[^\\s]+";
    Pattern r = Pattern.compile(pattern);
    Matcher m = r.matcher(sanitizedInputFormula);

    while (m.find()) {
      String match = m.group();
      String bare = match.replace("define-fun ", ""); // to replace
      String replacement = "|" + bare.substring(1) + "|";
      checkState(!sanitizedInputFormula.contains(replacement));
      replacementMapBuilder.put(bare, replacement);
      // TODO: can we modify the string while we match?
    }

    for (Entry<String, String> replacementEntry : replacementMapBuilder.buildOrThrow().entrySet()) {
      sanitizedInputFormula =
          sanitizedInputFormula.replace(replacementEntry.getKey(), replacementEntry.getValue());
    }
    checkState(!sanitizedInputFormula.contains("define-fun ."));
    return sanitizedInputFormula;
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

  @Override
  public String dumpFormulaImpl(Term f) {
    assert getFormulaCreator().getFormulaType(f) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";

    StringBuilder variablesAndUFsAsSMTLIB2 = getAllDeclaredVariablesAndUFsAsSMTLIB2(f);

    // Add the final assert after the declarations
    variablesAndUFsAsSMTLIB2.append("(assert ").append(f).append(')');
    return variablesAndUFsAsSMTLIB2.toString();
  }

  private StringBuilder getAllDeclaredVariablesAndUFsAsSMTLIB2(Term f) {
    // get all symbols
    ImmutableMap.Builder<String, Term> allKnownVarsAndUFsBuilder = ImmutableMap.builder();
    creator.extractVariablesAndUFs(f, true, allKnownVarsAndUFsBuilder::put);

    // return all symbols relevant for the input term as SMTLIB2
    StringBuilder builder = new StringBuilder();
    // buildKeepingLast due to UFs; 1 UF might be applied multiple times. But the names and the
    // types are consistent.
    getSMTLIB2DeclarationsFor(allKnownVarsAndUFsBuilder.buildKeepingLast()).forEach(builder::append);
    return builder;
  }

  /**
   * Returns the SMTLIB2 declarations for the input, line by line with one declaration per line,
   * with a line-break at the end of all lines.
   */
  private static Set<String> getSMTLIB2DeclarationsFor(Map<String, Term> varsAndUFs) {
    ImmutableSet.Builder<String> variablesAndUFsAsSMTLIB2 = ImmutableSet.builder();
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
      variablesAndUFsAsSMTLIB2.add(line.toString());
    }
    return variablesAndUFsAsSMTLIB2.build();
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

  private Command getNextCommand(InputParser parser) {
    try {
      // throws CVC5ParserException for errors
      return parser.nextCommand();
    } catch (Exception parseException) {
      throw new IllegalArgumentException(
          "Error parsing with CVC5: " + parseException.getMessage(), parseException);
    }
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

  private static Term getAssertedTerm(
      Solver parseSolver, int numberOfAssertions, boolean mathsatReplacementUsed) {
    Term[] assertions = parseSolver.getAssertions();
    checkArgument(
        numberOfAssertions > 0,
        "Error when parsing using CVC5: at least one assert "
            + "statement needs to be part of the input");

    // If failing, conjugate the input and return
    // (We disallow push and pop currently, so this is fine!)
    // TODO: this can be improved, but we need to be able to discern the non-assertion terms to
    //  re-substitute (we can just remember them before invoking the commands above)
    checkArgument(
        numberOfAssertions == 1,
        "Error when parsing using CVC5: at most one assert "
            + "statement is currently allowed to be part of the input");
    checkArgument(assertions.length > 0, "Error when parsing using CVC5: no term found to return");
    Term parsedTerm = assertions[assertions.length - 1];
    checkState(!checkNotNull(parsedTerm).isNull());

    if (assertions.length > 1) {
      // Sometimes terms are added as assertions without them being sources by an assertion, but
      // a fun-def. We re-substitute these! (E.g. MathSAT5 input)
      for (int i = assertions.length - 2; i >= 0; i--) {
        Term equation = assertions[i];

        try {
          if (equation.getKind() != Kind.EQUAL) {
            // Original problem we try to solve
            if (mathsatReplacementUsed) {
              throw new IllegalArgumentException(
                  "Error when parsing using CVC5, no expressions may use a . or "
                      + "@ as first character in a symbol.");
            } else {
              throw new IllegalArgumentException(
                  "Error when parsing using CVC5: re-substitution of function-definitions into "
                      + "assertions failed");
            }
          }

          parsedTerm = parsedTerm.substitute(equation.getChild(0), equation.getChild(1));
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
