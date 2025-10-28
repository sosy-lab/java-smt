// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.base.Joiner;
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
import java.util.LinkedHashMap;
import java.util.Map;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

class CVC5FormulaManager extends AbstractFormulaManager<Term, Sort, TermManager, Term> {

  private final CVC5FormulaCreator creator;

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
    String expectedSuccessMsg = "success\n";
    parseSolver.setOption("print-success", "true");
    InputParser parser = new InputParser(parseSolver, sm);
    parser.setStringInput(InputLanguage.SMT_LIB_2_6, formulaStr, "");

    ImmutableSet.Builder<Term> substituteFromBuilder = ImmutableSet.builder();
    ImmutableSet.Builder<Term> substituteToBuilder = ImmutableSet.builder();

    Command command = parser.nextCommand();
    while (!command.isNull()) {
      if (command.toString().contains("push") || command.toString().contains("pop")) {
        // TODO: push and pop?
        throw new IllegalArgumentException(
            "Parsing SMTLIB2 with CVC5 in JavaSMT does not support" + " push or pop currently.");
      }

      // This WILL read in asserts, and they are no longer available for getTerm(), but on the
      // solver as assertions
      // invoke() throws CVC5ParserException for errors
      String invokeReturn = command.invoke(parseSolver, sm);
      if (!invokeReturn.equals(expectedSuccessMsg)) {
        throw new AssertionError("Unknown error when parsing using CVC5: " + invokeReturn);
      }
      command = parser.nextCommand();
    }

    parser.deletePointer(); // Clean up parser

    // Register new terms in our caches
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

        if (parsedSort.isFunction()) {
          // UFs
          Term funCacheHit = creator.functionsCache.get(parsedTermString);
          if (funCacheHit == null) {
            assert !creator.variablesCache.contains(parsedTermString, parsedSortString);
            creator.functionsCache.put(parsedTermString, termToRegister);

          } else {
            substituteFromBuilder.add(termToRegister);
            substituteToBuilder.add(funCacheHit);
          }

        } else {
          Term termCacheHit = creator.variablesCache.get(parsedTermString, parsedSortString);
          if (termCacheHit == null) {
            assert !creator.functionsCache.containsKey(parsedTermString);
            checkState(!creator.variablesCache.containsRow(parsedTermString));
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

    // TODO: Which terms can end up here? Seems like this is always empty
    checkState(sm.getNamedTerms().isEmpty());

    // Get the assertions out of the solver
    if (parseSolver.getAssertions().length != 1) {
      // If failing, conjugate the input and return
      throw new IllegalArgumentException(
          "Error when parsing using CVC5: more than 1 assertion in SMTLIB2 input");
    }
    Term parsedTerm = parseSolver.getAssertions()[0];
    checkState(!checkNotNull(parsedTerm).isNull());

    // If the symbols used in the term were already declared before parsing, the term uses new
    // ones with the same name, so we need to substitute them!
    ImmutableSet<Term> substituteFrom = substituteFromBuilder.build();
    ImmutableSet<Term> substituteTo = substituteToBuilder.build();
    checkState(substituteFrom.size() == substituteTo.size());
    assert substituteFrom.stream()
        .map(Term::toString)
        .allMatch(from -> substituteTo.stream().map(Term::toString).anyMatch(from::equals));
    parsedTerm =
        parsedTerm.substitute(
            substituteFrom.toArray(new Term[0]), substituteTo.toArray(new Term[0]));

    // Quantified formulas do not give us the bound variables in getDeclaredTerms() above.
    // Find them and register a free equivalent
    creator.registerBoundVariablesWithVisitor(parsedTerm);
    parseSolver.deletePointer(); // Clean up parse solver
    return parsedTerm;
  }

  @Override
  public String dumpFormulaImpl(Term f) {
    assert getFormulaCreator().getFormulaType(f) == FormulaType.BooleanType
        : "Only BooleanFormulas may be dumped";

    StringBuilder out = new StringBuilder();
    // get all symbols
    final Map<String, Term> allVars = new LinkedHashMap<>();
    creator.extractVariablesAndUFs(f, true, allVars::put);

    // print all symbols
    for (Map.Entry<String, Term> entry : allVars.entrySet()) {
      String name = entry.getKey();
      Term var = entry.getValue();

      // escaping is stolen from SMTInterpol, lets hope this remains consistent
      out.append("(declare-fun ").append(PrintTerm.quoteIdentifier(name)).append(" (");

      // add function parameters
      Iterable<Sort> childrenTypes;
      try {
        if (var.getSort().isFunction() || var.getKind() == Kind.APPLY_UF) {
          childrenTypes = Iterables.skip(Iterables.transform(var, Term::getSort), 1);
        } else {
          childrenTypes = Iterables.transform(var, Term::getSort);
        }
      } catch (CVC5ApiException e) {
        childrenTypes = Iterables.transform(var, Term::getSort);
      }
      out.append(Joiner.on(" ").join(childrenTypes));

      // and return type
      out.append(") ").append(var.getSort().toString()).append(")\n");
    }

    // now add the final assert
    out.append("(assert ").append(f).append(')');
    return out.toString();
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
}
