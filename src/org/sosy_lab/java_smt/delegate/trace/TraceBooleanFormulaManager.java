/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.delegate.trace;

import java.util.Arrays;
import java.util.Collection;
import java.util.Set;
import java.util.stream.Collector;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

public class TraceBooleanFormulaManager implements BooleanFormulaManager {
  private final BooleanFormulaManager delegate;
  private final TraceLogger logger;

  TraceBooleanFormulaManager(BooleanFormulaManager pDelegate, TraceLogger pLogger) {
    delegate = pDelegate;
    logger = pLogger;
  }

  @Override
  public BooleanFormula makeTrue() {
    return logger.logDef("mgr.getBooleanFormulaManager()", "makeTrue()", delegate::makeTrue);
  }

  @Override
  public BooleanFormula makeFalse() {
    return logger.logDef("mgr.getBooleanFormulaManager()", "makeFalse()", delegate::makeFalse);
  }

  @Override
  public BooleanFormula makeVariable(String pVar) {
    return logger.logDef(
        "mgr.getBooleanFormulaManager()",
        String.format("makeVariable(\"%s\")", pVar),
        () -> delegate.makeVariable(pVar));
  }

  @Override
  public BooleanFormula equivalence(BooleanFormula formula1, BooleanFormula formula2) {
    return logger.logDef(
        "mgr.getBooleanFormulaManager()",
        String.format(
            "equivalence(%s, %s)", logger.toVariable(formula1), logger.toVariable(formula2)),
        () -> delegate.equivalence(formula1, formula2));
  }

  @Override
  public BooleanFormula implication(BooleanFormula formula1, BooleanFormula formula2) {
    return logger.logDef(
        "mgr.getBooleanFormulaManager()",
        String.format(
            "implication(%s, %s)", logger.toVariable(formula1), logger.toVariable(formula2)),
        () -> delegate.implication(formula1, formula2));
  }

  @Override
  public boolean isTrue(BooleanFormula formula) {
    return logger.logDefDiscard(
        "mgr.getBooleanFormulaManager()",
        String.format("isTrue(%s)", logger.toVariable(formula)),
        () -> delegate.isTrue(formula));
  }

  @Override
  public boolean isFalse(BooleanFormula formula) {
    return logger.logDefDiscard(
        "mgr.getBooleanFormulaManager()",
        String.format("isFalse(%s)", logger.toVariable(formula)),
        () -> delegate.isFalse(formula));
  }

  @Override
  public <T extends Formula> T ifThenElse(BooleanFormula cond, T f1, T f2) {
    return logger.logDef(
        "mgr.getBooleanFormulaManager()",
        String.format(
            "ifThenElse(%s, %s, %s)",
            logger.toVariable(cond), logger.toVariable(f1), logger.toVariable(f2)),
        () -> delegate.ifThenElse(cond, f1, f2));
  }

  @Override
  public BooleanFormula not(BooleanFormula formula) {
    return logger.logDef(
        "mgr.getBooleanFormulaManager()",
        String.format("not(%s)", logger.toVariable(formula)),
        () -> delegate.not(formula));
  }

  @Override
  public BooleanFormula and(BooleanFormula formula1, BooleanFormula formula2) {
    return logger.logDef(
        "mgr.getBooleanFormulaManager()",
        String.format("and(%s, %s)", logger.toVariable(formula1), logger.toVariable(formula2)),
        () -> delegate.and(formula1, formula2));
  }

  @Override
  public BooleanFormula and(Collection<BooleanFormula> bits) {
    BooleanFormula f = makeTrue();
    for (BooleanFormula bf : bits) {
      f = and(bf, f);
    }
    return f;
  }

  @Override
  public BooleanFormula and(BooleanFormula... bits) {
    return and(Arrays.asList(bits));
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toConjunction() {
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanFormula or(BooleanFormula formula1, BooleanFormula formula2) {
    return logger.logDef(
        "mgr.getBooleanFormulaManager()",
        String.format("or(%s, %s)", logger.toVariable(formula1), logger.toVariable(formula2)),
        () -> delegate.or(formula1, formula2));
  }

  @Override
  public BooleanFormula or(Collection<BooleanFormula> bits) {
    BooleanFormula f = makeFalse();
    for (BooleanFormula bf : bits) {
      f = or(bf, f);
    }
    return f;
  }

  @Override
  public BooleanFormula or(BooleanFormula... bits) {
    return or(Arrays.asList(bits));
  }

  @Override
  public Collector<BooleanFormula, ?, BooleanFormula> toDisjunction() {
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanFormula xor(BooleanFormula bits1, BooleanFormula bits2) {
    return logger.logDef(
        "mgr.getBooleanFormulaManager()",
        String.format("xor(%s, %s)", logger.toVariable(bits1), logger.toVariable(bits2)),
        () -> delegate.xor(bits1, bits2));
  }

  @Override
  public <R> R visit(BooleanFormula pFormula, BooleanFormulaVisitor<R> visitor) {
    throw new UnsupportedOperationException();
  }

  @Override
  public void visitRecursively(
      BooleanFormula f, BooleanFormulaVisitor<TraversalProcess> rFormulaVisitor) {
    throw new UnsupportedOperationException();
  }

  @Override
  public BooleanFormula transformRecursively(
      BooleanFormula f, BooleanFormulaTransformationVisitor pVisitor) {
    throw new UnsupportedOperationException();
  }

  @Override
  public Set<BooleanFormula> toConjunctionArgs(BooleanFormula f, boolean flatten) {
    throw new UnsupportedOperationException();
  }

  @Override
  public Set<BooleanFormula> toDisjunctionArgs(BooleanFormula f, boolean flatten) {
    throw new UnsupportedOperationException();
  }
}
