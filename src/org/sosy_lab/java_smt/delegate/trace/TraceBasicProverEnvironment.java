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

import static org.sosy_lab.common.collect.Collections3.transformedImmutableListCopy;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.UserPropagator;

class TraceBasicProverEnvironment<T> implements BasicProverEnvironment<T> {
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
  public @Nullable T push(BooleanFormula f) throws InterruptedException {
    return logger.logDefKeep(
        logger.toVariable(this),
        "push(%s)".formatted(logger.toVariable(f)),
        () -> delegate.push(f));
  }

  @Override
  public void pop() {
    logger.logStmt(logger.toVariable(this), "pop()", delegate::pop);
  }

  @Override
  public @Nullable T addConstraint(BooleanFormula constraint) throws InterruptedException {
    return logger.logDefKeep(
        logger.toVariable(this),
        "addConstraint(%s)".formatted(logger.toVariable(constraint)),
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
    return logger.logDefKeep(logger.toVariable(this), "isUnsat()", delegate::isUnsat);
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> assumptions)
      throws SolverException, InterruptedException {
    return logger.logDefKeep(
        logger.toVariable(this),
        "isUnsatWithAssumptions(ImmutableList.of(%s))".formatted(logger.toVariables(assumptions)),
        () -> delegate.isUnsatWithAssumptions(assumptions));
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() throws SolverException {
    return logger.logDefKeep(
        logger.toVariable(this),
        "getModel()",
        () -> new TraceModel(delegate.getModel(), mgr, logger));
  }

  @SuppressWarnings("resource")
  @Override
  public Evaluator getEvaluator() throws SolverException {
    return logger.logDefKeep(
        logger.toVariable(this),
        "getEvaluator()",
        () -> new TraceEvaluator(delegate.getEvaluator(), mgr, logger));
  }

  @Override
  public ImmutableList<Model.ValueAssignment> getModelAssignments() throws SolverException {
    ImmutableList<Model.ValueAssignment> result =
        logger.logDefDiscard(
            logger.toVariable(this), "getModelAssignments()", delegate::getModelAssignments);
    return transformedImmutableListCopy(
        result,
        (Model.ValueAssignment assigment) -> {
          var key = mgr.rebuild(assigment.getKey());
          var val = mgr.rebuild(assigment.getValueAsFormula());
          var map = mgr.rebuild(assigment.getAssignmentAsFormula());
          return new Model.ValueAssignment(
              key,
              val,
              map,
              assigment.getName(),
              assigment.getValue(),
              assigment.getArgumentsInterpretation());
        });
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    return mgr.rebuildAll(
        logger.logDefDiscard(logger.toVariable(this), "getUnsatCore()", delegate::getUnsatCore));
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    return logger
        .logDefDiscard(
            logger.toVariable(this),
            "getUnsatCoreOverAssumptions(ImmutableList.of(%s))"
                .formatted(logger.toVariables(assumptions)),
            () -> delegate.unsatCoreOverAssumptions(assumptions))
        .map(mgr::rebuildAll);
  }

  @Override
  public ImmutableMap<String, String> getStatistics() {
    return delegate.getStatistics();
  }

  @Override
  public void close() {
    logger.logStmt(logger.toVariable(this), "close()", delegate::close);
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    return logger.logDefDiscard(
        logger.toVariable(this),
        "delegate.allSat(new AllSatCallback<>() {"
            + "  public void apply(List<BooleanFormula> model) {}"
            + "  public R getResult() { throw new UnsupportedOperationException(); }"
            + "}, ImmutableList.of(%s));".formatted(logger.toVariables(important)),
        () ->
            delegate.allSat(
                new AllSatCallback<>() {
                  @Override
                  public void apply(List<BooleanFormula> model) {
                    var newModel = mgr.rebuildAll(model);
                    callback.apply(newModel);
                  }

                  @Override
                  public R getResult() throws InterruptedException {
                    return callback.getResult();
                  }
                },
                important));
  }

  @Override
  public boolean registerUserPropagator(UserPropagator propagator) {
    throw new UnsupportedOperationException();
  }
}
