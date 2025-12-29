// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Kind;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import io.github.cvc5.TermManager;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
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
    checkArgument(
        pT instanceof CVC5Formula,
        "Cannot get the CVC5 term of type " + pT.getClass().getSimpleName() + " in the Solver!");
    return ((CVC5Formula) pT).getTerm();
  }

  @Override
  public Term equalImpl(Collection<Term> pArgs) {
    return getEnvironment().mkTerm(Kind.EQUAL, pArgs.toArray(new Term[0]));
  }

  @Override
  public Term distinctImpl(Collection<Term> pArgs) {
    return getEnvironment().mkTerm(Kind.DISTINCT, pArgs.toArray(new Term[0]));
  }

  @Override
  public Term parseImpl(String smtQuery) throws IllegalArgumentException {
    return new CVC5Parser(creator, this).parse(smtQuery);
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
  StringBuilder getSMTLIB2DeclarationsFor(ImmutableMap<String, Term> varsAndUFs) {
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
    Term substitutedTerm = substitute(extractInfo(f), castedMap);
    return getFormulaCreator().encapsulate(getFormulaType(f), substitutedTerm);
  }

  Term substitute(Term parsedTerm, Map<Term, Term> fromToMapping) {
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
}
