// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import opensmt.MainSolver;
import opensmt.PTRef;
import opensmt.SMTConfig;
import opensmt.sstat;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.basicimpl.ShutdownHook;

public abstract class OpenSmtAbstractProver<T> extends AbstractProverWithAllSat<T> {

  protected final OpenSmtFormulaCreator creator;
  protected final MainSolver osmtSolver;
  protected final SMTConfig config;
  protected final Deque<List<PTRef>> assertedFormulas = new ArrayDeque<>();

  private boolean changedSinceLastSatQuery = false;

  protected OpenSmtAbstractProver(
      OpenSmtFormulaCreator pFormulaCreator,
      FormulaManager pMgr,
      ShutdownNotifier pShutdownNotifier,
      SMTConfig pConfig,
      Set<ProverOptions> pOptions) {
    super(pOptions, pMgr.getBooleanFormulaManager(), pShutdownNotifier);

    creator = pFormulaCreator;

    // BUGFIX: We need to store the SMTConfig reference here to make sure the underlying C++ object does not get garbage collected
    config = pConfig;
    osmtSolver = new MainSolver(creator.getEnv(), pConfig, "JavaSmt");

    assertedFormulas.push(new ArrayList<>()); // create initial level

    // FIXME Handle prover options
    // if (pOptions.contains(ProverOptions.GENERATE_MODELS)) {
    //   solver.setOption("produce-models", "true");

    // FIXME Disable Model generation if arrays are required
    // https://github.com/usi-verification-and-security/opensmt/issues/630
  }

  protected static SMTConfig getConfigInstance(int randomSeed, boolean interpolation) {
    SMTConfig config = new SMTConfig();
    config.setRandomSeed(randomSeed);
    config.setInterpolation(interpolation);
    return config;
  }

  final MainSolver getOsmtSolver() {
    return osmtSolver;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    setChanged();
    assertedFormulas.push(new ArrayList<>());
    osmtSolver.push();
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    setChanged();
    Preconditions.checkState(size() > 0, "Tried to pop from an empty solver stack");
    assertedFormulas.pop();
    osmtSolver.pop();
  }

  @Nullable
  protected abstract T getConstraintName(BooleanFormula pF);

  @Override
  @Nullable
  public T addConstraint(BooleanFormula pF) throws InterruptedException {
    Preconditions.checkState(!closed);
    setChanged();

    PTRef exp = creator.extractInfo(pF);
    osmtSolver.insertFormula(exp);

    T label = getConstraintName(pF);
    assertedFormulas.peek().add(exp);
    return label;
  }

  @SuppressWarnings("resource")
  @Override
  public Model getModel() {
    List<PTRef> assertedTerms = new ArrayList<>();
    assertedFormulas.forEach(assertedTerms::addAll);
    return new OpenSmtModel(this, creator, assertedTerms);
  }

  @Override
  public Evaluator getEvaluator() {
    Preconditions.checkState(!closed);
    checkGenerateModels();
    return getEvaluatorWithoutChecks();
  }

  @SuppressWarnings("resource")
  @Override
  protected Evaluator getEvaluatorWithoutChecks() {
    return registerEvaluator(new OpenSmtEvaluator(this, creator));
  }

  protected void setChanged() {
    if (!changedSinceLastSatQuery) {
      changedSinceLastSatQuery = true;
      closeAllEvaluators();
    }
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    Preconditions.checkState(!closed);
    Preconditions.checkState(!changedSinceLastSatQuery);
    return super.getModelAssignments();
  }

  @Override
  @SuppressWarnings("try")
  public boolean isUnsat() throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    closeAllEvaluators();
    changedSinceLastSatQuery = false;

    try (ShutdownHook listener = new ShutdownHook(shutdownNotifier, osmtSolver::stop)) {
      shutdownNotifier.shutdownIfNecessary();
      sstat r = osmtSolver.check();
      shutdownNotifier.shutdownIfNecessary();

      if (r.isError()) {
        throw new SolverException("Error in Mainsolver.check()");
      }
      if (r.isUndef()) {
        throw new InterruptedException();
      }
      return r.isFalse();
    }
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    throw new UnsupportedOperationException("OpenSMT does not support unsat core.");
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("OpenSMT does not support unsat core.");
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("OpenSMT does not support unsat core.");
  }

  protected Collection<PTRef> getAssertedExpressions() {
    List<PTRef> result = new ArrayList<>();
    assertedFormulas.forEach(result::addAll);
    return result;
  }

  @Override
  public void close() {
    if (!closed) {
      closed = true;
      assertedFormulas.clear();
      osmtSolver.delete();
    }
    super.close();
  }

  @Override
  public int size() {
    Preconditions.checkState(!closed);
    return assertedFormulas.size() - 1;
  }
}
