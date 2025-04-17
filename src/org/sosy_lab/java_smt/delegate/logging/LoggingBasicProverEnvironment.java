// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.logging;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.logging.Level;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.proofs.ProofNode;

/** Wraps a basic prover environment with a logging object. */
class LoggingBasicProverEnvironment<T> implements BasicProverEnvironment<T> {

  private final BasicProverEnvironment<T> wrapped;
  final LogManager logger;

  private int level = 0;

  LoggingBasicProverEnvironment(BasicProverEnvironment<T> pWrapped, LogManager pLogger) {
    wrapped = checkNotNull(pWrapped);
    logger = checkNotNull(pLogger);
  }

  @Override
  public @Nullable T push(BooleanFormula f) throws InterruptedException {
    logger.log(Level.FINE, "up to level " + level++);
    logger.log(Level.FINE, "formula pushed:", f);
    return wrapped.push(f);
  }

  @Override
  public void pop() {
    logger.log(Level.FINER, "down to level " + level--);
    wrapped.pop();
  }

  @Override
  public @Nullable T addConstraint(BooleanFormula constraint) throws InterruptedException {
    return wrapped.addConstraint(constraint);
  }

  @Override
  public void push() throws InterruptedException {
    logger.log(Level.FINE, "up to level " + level++);
    wrapped.push();
  }

  @Override
  public int size() {
    int result = wrapped.size();
    Preconditions.checkState(result == level);
    logger.log(Level.FINE, "number of levels " + result);
    return result;
  }

  @Override
  public boolean isUnsat() throws SolverException, InterruptedException {
    boolean result = wrapped.isUnsat();
    logger.log(Level.FINE, "unsat-check returned:", result);
    return result;
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    logger.log(Level.FINE, "assumptions:", pAssumptions);
    boolean result = wrapped.isUnsatWithAssumptions(pAssumptions);
    logger.log(Level.FINE, "unsat-check returned:", result);
    return result;
  }

  @Override
  public Model getModel() throws SolverException {
    Model m = wrapped.getModel();
    logger.log(Level.FINE, "model", m);
    return m;
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    ImmutableList<ValueAssignment> m = wrapped.getModelAssignments();
    logger.log(Level.FINE, "model", m);
    return m;
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    List<BooleanFormula> unsatCore = wrapped.getUnsatCore();
    logger.log(Level.FINE, "unsat-core", unsatCore);
    return unsatCore;
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> assumptions) throws SolverException, InterruptedException {
    Optional<List<BooleanFormula>> result = wrapped.unsatCoreOverAssumptions(assumptions);
    logger.log(Level.FINE, "unsat-check returned:", result.isEmpty());
    return result;
  }

  @Override
  public ImmutableMap<String, String> getStatistics() {
    return wrapped.getStatistics();
  }

  @Override
  public ProofNode getProof() throws SolverException, InterruptedException {
    ProofNode p = wrapped.getProof();
    logger.log(Level.FINE, "proof", p);
    return p;
  }

  @Override
  public void close() {
    wrapped.close();
    logger.log(Level.FINER, "closed");
  }

  @Override
  public String toString() {
    return wrapped.toString();
  }

  @Override
  public <R> R allSat(AllSatCallback<R> callback, List<BooleanFormula> important)
      throws InterruptedException, SolverException {
    R result = wrapped.allSat(callback, important);
    logger.log(Level.FINE, "allsat-result:", result);
    return result;
  }
}
