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
import java.util.Collection;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;

public class CVC5BooleanFormulaManager
    extends AbstractBooleanFormulaManager<Term, Sort, Solver, Term> {

  private final Solver solver;

  protected CVC5BooleanFormulaManager(CVC5FormulaCreator pCreator) {
    super(pCreator);
    solver = pCreator.getEnv();
  }

  @Override
  protected Term makeVariableImpl(String pVar) {
    return formulaCreator.makeVariable(getFormulaCreator().getBoolType(), pVar);
  }

  @Override
  protected Term makeBooleanImpl(boolean pValue) {
    return solver.mkBoolean(pValue);
  }

  @Override
  protected Term not(Term pParam1) {
    return solver.mkTerm(Kind.NOT, pParam1);
  }

  @Override
  protected Term and(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.AND, pParam1, pParam2);
  }

  @Override
  protected Term andImpl(Collection<Term> pParams) {
    return solver.mkTerm(Kind.AND, pParams.toArray(new Term[0]));
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toConjunction() {
    return Collectors.collectingAndThen(Collectors.toList(), this::and);
  }

  @Override
  protected Term or(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.OR, pParam1, pParam2);
  }

  @Override
  protected Term orImpl(Collection<Term> pParams) {
    return solver.mkTerm(Kind.OR, pParams.toArray(new Term[0]));
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toDisjunction() {
    return Collectors.collectingAndThen(Collectors.toList(), this::or);
  }

  @Override
  protected Term xor(Term pParam1, Term pParam2) {
    return solver.mkTerm(Kind.XOR, pParam1, pParam2);
  }

  @Override
  protected Term equivalence(Term pBits1, Term pBits2) {
    return solver.mkTerm(Kind.EQUAL, pBits1, pBits2);
  }

  @Override
  protected boolean isTrue(Term pBits) {
    return pBits.isBooleanValue() && pBits.getBooleanValue();
  }

  @Override
  protected boolean isFalse(Term pBits) {
    return pBits.isBooleanValue() && !pBits.getBooleanValue();
  }

  @Override
  protected Term ifThenElse(Term pCond, Term pF1, Term pF2) {
    return solver.mkTerm(Kind.ITE, pCond, pF1, pF2);
  }
}
