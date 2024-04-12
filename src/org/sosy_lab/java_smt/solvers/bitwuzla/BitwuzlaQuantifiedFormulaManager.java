// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.List;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Kind;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Map_TermTerm;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Sort;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Term;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.TermManager;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Vector_Int;
import org.sosy_lab.java_smt.solvers.bitwuzla.api.Vector_Term;

public class BitwuzlaQuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<Term, Sort, Void, BitwuzlaDeclaration> {
  private final TermManager termManager;

  protected BitwuzlaQuantifiedFormulaManager(BitwuzlaFormulaCreator pCreator) {
    super(pCreator);
    termManager = pCreator.getTermManager();
  }

  @Override
  protected Term eliminateQuantifiers(Term pExtractInfo)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("Bitwuzla does not support eliminating Quantifiers.");
  }

  @Override
  public Term mkQuantifier(Quantifier q, List<Term> vars, Term body) {
    checkArgument(
        !vars.isEmpty(), "The list of bound variables for a quantifier may not be empty.");
    Term[] origVars = new Term[vars.size()];
    Term[] substVars = new Term[vars.size()];

    for (int i = 0; i < vars.size(); i++) {
      Term var = vars.get(i);
      origVars[i] = var;
      // Create/Use bound vars
      Term boundCopy = ((BitwuzlaFormulaCreator) formulaCreator).makeBoundVariable(var);
      substVars[i] = boundCopy;
    }

    Map_TermTerm map = new Map_TermTerm();
    for (int i = 0; i < origVars.length; i++) {
      map.put(origVars[i], substVars[i]);
    }
    body = termManager.substitute_term(body, map);

    Term currentFormula = body;
    for (int i = 0; i < vars.size(); i++) {
      Term[] argsAndBody = new Term[2];
      argsAndBody[0] = substVars[i];
      argsAndBody[1] = currentFormula;
      if (q.equals(Quantifier.FORALL)) {
        currentFormula =
            termManager.mk_term(Kind.FORALL, new Vector_Term(argsAndBody), new Vector_Int());

      } else {
        currentFormula =
            termManager.mk_term(Kind.EXISTS, new Vector_Term(argsAndBody), new Vector_Int());
      }
    }
    return currentFormula;
  }
}
