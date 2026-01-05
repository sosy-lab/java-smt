/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.parsing;

import java.util.Collection;
import java.util.Set;
import java.util.stream.Collector;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;
import org.sosy_lab.java_smt.delegate.parsing.ParsingFormulaManager.SymbolManager;

public class ParsingBooleanFormulaManager implements BooleanFormulaManager {
  private final SymbolManager symbolManager;
  private final BooleanFormulaManager delegate;

  public ParsingBooleanFormulaManager(
      SymbolManager pSymbolManager, BooleanFormulaManager pDelegate) {
    symbolManager = pSymbolManager;
    delegate = pDelegate;
  }

  @Override
  public BooleanFormula makeTrue() {
    return delegate.makeTrue();
  }

  @Override
  public BooleanFormula makeFalse() {
    return delegate.makeFalse();
  }

  @Override
  public BooleanFormula makeVariable(String pVar) {
    var term = delegate.makeVariable(pVar);
    symbolManager.addConstant(pVar, term);
    return term;
  }

  @Override
  public BooleanFormula equivalence(BooleanFormula formula1, BooleanFormula formula2) {
    return delegate.equivalence(formula1, formula2);
  }

  @Override
  public BooleanFormula implication(BooleanFormula formula1, BooleanFormula formula2) {
    return delegate.implication(formula1, formula2);
  }

  @Override
  public boolean isTrue(BooleanFormula formula) {
    return delegate.isTrue(formula);
  }

  @Override
  public boolean isFalse(BooleanFormula formula) {
    return delegate.isFalse(formula);
  }

  @Override
  public <T extends Formula> T ifThenElse(BooleanFormula cond, T f1, T f2) {
    return delegate.ifThenElse(cond, f1, f2);
  }

  @Override
  public BooleanFormula not(BooleanFormula bits) {
    return delegate.not(bits);
  }

  @Override
  public BooleanFormula and(BooleanFormula bits1, BooleanFormula bits2) {
    return delegate.and(bits1, bits2);
  }

  @Override
  public BooleanFormula and(Collection<BooleanFormula> bits) {
    return delegate.and(bits);
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toConjunction() {
    return delegate.toConjunction();
  }

  @Override
  public BooleanFormula or(BooleanFormula bits1, BooleanFormula bits2) {
    return delegate.or(bits1, bits2);
  }

  @Override
  public BooleanFormula or(Collection<BooleanFormula> bits) {
    return delegate.or(bits);
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toDisjunction() {
    return delegate.toDisjunction();
  }

  @Override
  public BooleanFormula xor(BooleanFormula bits1, BooleanFormula bits2) {
    return delegate.xor(bits1, bits2);
  }

  @Override
  public <R> R visit(BooleanFormula pFormula, BooleanFormulaVisitor<R> visitor) {
    return delegate.visit(pFormula, visitor);
  }

  @Override
  public void visitRecursively(
      BooleanFormula f, BooleanFormulaVisitor<TraversalProcess> rFormulaVisitor) {
    delegate.visitRecursively(f, rFormulaVisitor);
  }

  @Override
  public BooleanFormula transformRecursively(
      BooleanFormula f, BooleanFormulaTransformationVisitor pVisitor) {
    return delegate.transformRecursively(f, pVisitor);
  }

  @Override
  public Set<BooleanFormula> toConjunctionArgs(BooleanFormula f, boolean flatten) {
    return delegate.toConjunctionArgs(f, flatten);
  }

  @Override
  public Set<BooleanFormula> toDisjunctionArgs(BooleanFormula f, boolean flatten) {
    return delegate.toDisjunctionArgs(f, flatten);
  }
}
