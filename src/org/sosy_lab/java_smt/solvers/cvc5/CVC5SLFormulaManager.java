// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import io.github.cvc5.Kind;
import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import org.sosy_lab.java_smt.basicimpl.AbstractSLFormulaManager;

public class CVC5SLFormulaManager extends AbstractSLFormulaManager<Term, Sort, Solver, Term> {

  private final Solver solver;

  protected CVC5SLFormulaManager(CVC5FormulaCreator pCreator) {
    super(pCreator);
    solver = pCreator.getEnv();
  }

  @Override
  protected Term makeStar(Term e1, Term e2) {
    return solver.mkTerm(Kind.SEP_STAR, e1, e2);
  }

  @Override
  protected Term makePointsTo(Term pPtr, Term pTo) {
    return solver.mkTerm(Kind.SEP_PTO, pPtr, pTo);
  }

  @Override
  protected Term makeMagicWand(Term pE1, Term pE2) {
    return solver.mkTerm(Kind.SEP_WAND, pE1, pE2);
  }

  @Override
  protected Term makeEmptyHeap(Sort pT1, Sort pT2) {
    // According to the documentation this is sortless
    return solver.mkTerm(Kind.SEP_EMP);
  }

  @Override
  protected Term makeNilElement(Sort pSort) {
    return solver.mkSepNil(pSort);
  }
}
