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

import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

public class TraceProverEnvironment implements ProverEnvironment {
  private final ProverEnvironment delegate;
  private final TraceLogger logger;

  TraceProverEnvironment(ProverEnvironment pDelegate, TraceLogger pLogger) {
    delegate = pDelegate;
    logger = pLogger;
  }

  @Override
  public void pop() {
    logger.logStmt(logger.toVariable(this), "pop()", delegate::pop);
  }

  @Override
  public @Nullable Void addConstraint(BooleanFormula constraint) throws InterruptedException {
    return logger.logDef(
        logger.toVariable(this),
        String.format("addConstraint(%s)", logger.toVariable(constraint)),
        () -> delegate.addConstraint(constraint));
  }

  @Override
  public void push() throws InterruptedException {
    logger.logStmt(logger.toVariable(this), "push()", delegate::push);
  }

  @Override
  public int size() {
    return delegate.size();
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    return logger.logDef(logger.toVariable(this), "isUnsat()", delegate::isUnsat);
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException();
  }

  @Override
  public Model getModel() throws SolverException {
    return logger.logDef(
        logger.toVariable(this), "getModel()", () -> new TraceModel(delegate.getModel(), logger));
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    throw new UnsupportedOperationException();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    throw new UnsupportedOperationException();
  }

  @Override
  public void close() {
    logger.logStmt(logger.toVariable(this), "close()", delegate::close);
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    throw new UnsupportedOperationException();
  }
}
