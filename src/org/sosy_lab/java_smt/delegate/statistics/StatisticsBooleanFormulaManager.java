// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Set;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

class StatisticsBooleanFormulaManager implements BooleanFormulaManager {

  private final BooleanFormulaManager delegate;
  private final SolverStatistics stats;

  StatisticsBooleanFormulaManager(BooleanFormulaManager pDelegate, SolverStatistics pStats) {
    delegate = checkNotNull(pDelegate);
    stats = checkNotNull(pStats);
  }

  @Override
  public BooleanFormula makeTrue() {
    stats.booleanOperations.getAndIncrement();
    return delegate.makeTrue();
  }

  @Override
  public BooleanFormula makeFalse() {
    stats.booleanOperations.getAndIncrement();
    return delegate.makeFalse();
  }

  @Override
  public BooleanFormula makeVariable(String pVar) {
    stats.booleanOperations.getAndIncrement();
    return delegate.makeVariable(pVar);
  }

  @Override
  public BooleanFormula equivalence(BooleanFormula pFormula1, BooleanFormula pFormula2) {
    stats.booleanOperations.getAndIncrement();
    return delegate.equivalence(pFormula1, pFormula2);
  }

  @Override
  public BooleanFormula implication(BooleanFormula pFormula1, BooleanFormula pFormula2) {
    stats.booleanOperations.getAndIncrement();
    return delegate.implication(pFormula1, pFormula2);
  }

  @Override
  public boolean isTrue(BooleanFormula pFormula) {
    stats.booleanOperations.getAndIncrement();
    return delegate.isTrue(pFormula);
  }

  @Override
  public boolean isFalse(BooleanFormula pFormula) {
    stats.booleanOperations.getAndIncrement();
    return delegate.isFalse(pFormula);
  }

  @Override
  public <T extends Formula> T ifThenElse(BooleanFormula pCond, T pF1, T pF2) {
    stats.booleanOperations.getAndIncrement();
    return delegate.ifThenElse(pCond, pF1, pF2);
  }

  @Override
  public BooleanFormula not(BooleanFormula pBits) {
    stats.booleanOperations.getAndIncrement();
    return delegate.not(pBits);
  }

  @Override
  public BooleanFormula and(BooleanFormula pBits1, BooleanFormula pBits2) {
    stats.booleanOperations.getAndIncrement();
    return delegate.and(pBits1, pBits2);
  }

  @Override
  public BooleanFormula and(Collection<BooleanFormula> pBits) {
    stats.booleanOperations.getAndIncrement();
    return delegate.and(pBits);
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toConjunction() {
    return Collectors.collectingAndThen(Collectors.toList(), this::and);
  }

  @Override
  public BooleanFormula or(BooleanFormula pBits1, BooleanFormula pBits2) {
    stats.booleanOperations.getAndIncrement();
    return delegate.or(pBits1, pBits2);
  }

  @Override
  public BooleanFormula or(Collection<BooleanFormula> pBits) {
    stats.booleanOperations.getAndIncrement();
    return delegate.or(pBits);
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toDisjunction() {
    return Collectors.collectingAndThen(Collectors.toList(), this::or);
  }

  @Override
  public BooleanFormula xor(BooleanFormula pBits1, BooleanFormula pBits2) {
    stats.booleanOperations.getAndIncrement();
    return delegate.xor(pBits1, pBits2);
  }

  @Override
  public <R> R visit(BooleanFormula pFormula, BooleanFormulaVisitor<R> pVisitor) {
    stats.visits.getAndIncrement();
    return delegate.visit(pFormula, pVisitor);
  }

  @Override
  public void visitRecursively(
      BooleanFormula pF, BooleanFormulaVisitor<TraversalProcess> pRFormulaVisitor) {
    stats.visits.getAndIncrement();
    delegate.visitRecursively(pF, pRFormulaVisitor);
  }

  @Override
  public BooleanFormula transformRecursively(
      BooleanFormula pF, BooleanFormulaTransformationVisitor pVisitor) {
    stats.visits.getAndIncrement();
    return delegate.transformRecursively(pF, pVisitor);
  }

  @Override
  public Set<BooleanFormula> toConjunctionArgs(BooleanFormula pF, boolean pFlatten) {
    return delegate.toConjunctionArgs(pF, pFlatten);
  }

  @Override
  public Set<BooleanFormula> toDisjunctionArgs(BooleanFormula pF, boolean pFlatten) {
    return delegate.toDisjunctionArgs(pF, pFlatten);
  }
}
