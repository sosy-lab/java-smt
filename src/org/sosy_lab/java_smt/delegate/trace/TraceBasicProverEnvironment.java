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
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverException;

public class TraceBasicProverEnvironment<T> implements BasicProverEnvironment<T> {
  private final BasicProverEnvironment<T> delegate;

  private final TraceFormulaManager mgr;
  private final TraceLogger logger;

  TraceBasicProverEnvironment(
      BasicProverEnvironment<T> pDelegate,
      TraceFormulaManager pFormulaManager,
      TraceLogger pLogger) {
    delegate = pDelegate;
    mgr = pFormulaManager;
    logger = pLogger;
  }

  @Override
  public void pop() {
    logger.logStmt(logger.toVariable(this), "pop()", delegate::pop);
  }

  @Override
  public @Nullable T addConstraint(BooleanFormula constraint) throws InterruptedException {
    String var = logger.newVariable();
    logger.appendDef(
        var,
        String.format(
            "%s.addConstraint(%s)", logger.toVariable(this), logger.toVariable(constraint)));
    T f = delegate.addConstraint(constraint);
    logger.mapVariable(var, f);
    return f;
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
    String var = logger.newVariable();
    logger.appendDef(var, String.format("%s.isUnsat()", logger.toVariable(this)));
    boolean unsat = delegate.isUnsat();
    logger.mapVariable(var, unsat);
    return unsat;
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    String var = logger.newVariable();
    logger.appendDef(
        var,
        String.format(
            "%s.isUnsatWithAssumptions(ImmutableList.of(%s))",
            logger.toVariable(this), logger.toVariables(assumptions)));
    boolean unsat = delegate.isUnsatWithAssumptions(assumptions);
    logger.mapVariable(var, unsat);
    return unsat;
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException {
    String var = logger.newVariable();
    logger.appendDef(var, String.format("%s.getModel()", logger.toVariable(this)));
    Model model = new TraceModel(delegate.getModel(), mgr, logger);
    logger.mapVariable(var, model);
    return model;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    logger.appendStmt(String.format("%s.getUnsatCore()", logger.toVariable(this)));
    List<BooleanFormula> core = delegate.getUnsatCore();
    logger.undoLast();
    return mgr.rebuildAll(core);
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    logger.appendStmt(
        String.format(
            "%s.getUnsatCoreOverAssumptions(ImmutableList.of(%s))",
            logger.toVariable(this), logger.toVariables(assumptions)));
    Optional<List<BooleanFormula>> maybeCore = delegate.unsatCoreOverAssumptions(assumptions);
    logger.undoLast();
    return maybeCore.map(mgr::rebuildAll);
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
