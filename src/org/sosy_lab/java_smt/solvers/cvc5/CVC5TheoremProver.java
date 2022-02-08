// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import edu.stanford.CVC4.ExprManagerMapCollection;
import edu.stanford.CVC4.SmtEngine;
import io.github.cvc5.api.Result;
import io.github.cvc5.api.Solver;
import io.github.cvc5.api.Term;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.solvers.cvc4.CVC4Model;

class CVC5TheoremProver extends AbstractProverWithAllSat<Void>
    implements ProverEnvironment, BasicProverEnvironment<Void> {

  private final CVC5FormulaCreator creator;
  Solver solver;
  private boolean changedSinceLastSatQuery = false;

  /** Tracks formulas on the stack, needed for model generation. */
  protected final Deque<List<Term>> assertedFormulas = new ArrayDeque<>();

  /**
   * Tracks provided models to inform them when the SmtEngine is closed. We can no longer access
   * model evaluation after closing the SmtEngine.
   */
  private final Set<CVC5Model> models = new LinkedHashSet<>();

  /** We copy expression between different ExprManagers. The map serves as cache. */
  private final ExprManagerMapCollection exportMapping = new ExprManagerMapCollection();

  // TODO: does CVC5 support separation logic in incremental mode?
  private final boolean incremental;

  protected CVC5TheoremProver(
      CVC5FormulaCreator pFormulaCreator,
      ShutdownNotifier pShutdownNotifier,
      int randomSeed,
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr,
      Solver pSolver) {
    super(pOptions, pBmgr, pShutdownNotifier);

    creator = pFormulaCreator;
    solver = pSolver;
    incremental = !enableSL;
    assertedFormulas.push(new ArrayList<>()); // create initial level
    solver = pSolver;
  }

  private void setOptions(int randomSeed, Set<ProverOptions> pOptions) {
    solver.setOption("incremental", "incremental");
    if (pOptions.contains(ProverOptions.GENERATE_MODELS)) {
      solver.setOption("produce-models", "true");
    }
    if (pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE)) {
      solver.setOption("produce-unsat-cores", "true");
    }
    solver.setOption("produce-assertions", "true");
    solver.setOption("dump-models", "true");
    solver.setOption("output-language", "smt2");
    solver.setOption("random-seed", String.valueOf(randomSeed));
    // Set Strings option to enable all String features (such as lessOrEquals)
    solver.setOption("strings-exp", "true");
    // Enable more complete quantifier solving (for more information see
    // CVC5QuantifiedFormulaManager)
    solver.setOption("full-saturate-quant", "true");
  }

  protected void setOptionForIncremental() {
    solver.setOption("incremental", "true");
  }

  /** import an expression from global context into this prover's context. */
  protected Term importExpr(Term term) {
    // TODO: currently not supported! They are working on it. See CVC5 github discussion.
    return null;
  }

  /** export an expression from this prover's context into global context. */
  protected Term exportExpr(Term expr) {
    // TODO: currently not supported! They are working on it. See CVC5 github discussion.
    return null;
  }

  @Override
  public void push() {
    Preconditions.checkState(!closed);
    setChanged();
    assertedFormulas.push(new ArrayList<>());
    if (incremental) {
      solver.push();
    }
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    setChanged();
    assertedFormulas.pop();
    Preconditions.checkState(!assertedFormulas.isEmpty(), "initial level must remain until close");
    if (incremental) {
      solver.pop();
    }
  }

  @Override
  public @Nullable Void addConstraint(BooleanFormula pF) throws InterruptedException {
    Preconditions.checkState(!closed);
    setChanged();
    Term exp = creator.extractInfo(pF);
    assertedFormulas.peek().add(exp);
    if (incremental) {
      solver.assertFormula(exp);
    }
    return null;
  }

  @Override
  public CVC4Model getModel() {
    Preconditions.checkState(!closed);
    checkGenerateModels();
    return getModelWithoutChecks();
  }

  @Override
  protected CVC4Model getModelWithoutChecks() {
    Preconditions.checkState(!changedSinceLastSatQuery);
    CVC5Model model = new CVC5Model(this, creator, getAssertedExpressions());
    models.add(model);
    return model;
  }

  void unregisterModel(CVC5Model model) {
    models.remove(model);
  }

  private void setChanged() {
    if (!changedSinceLastSatQuery) {
      changedSinceLastSatQuery = true;
      closeAllModels();
      if (!incremental) {
        // create a new clean smtEngine
        smtEngine = new SmtEngine(exprManager);
      }
    }
  }

  /**
   * whenever the SmtEngine changes, we need to invalidate all models.
   *
   * <p>See for details <a href="https://github.com/CVC4/CVC4/issues/2648">Issue 2648</a> . This is
   * legacy CVC4. TODO: decide whether we need this or not
   */
  private void closeAllModels() {
    for (CVC5Model model : ImmutableList.copyOf(models)) {
      model.close();
    }
    Preconditions.checkState(models.isEmpty(), "all models should be closed");
  }

  @Override
  public ImmutableList<ValueAssignment> getModelAssignments() throws SolverException {
    Preconditions.checkState(!closed);
    Preconditions.checkState(!changedSinceLastSatQuery);
    try (CVC5Model model = getModel()) {
      return model.toList();
    }
  }

  @Override
  @SuppressWarnings("try")
  public boolean isUnsat() throws InterruptedException, SolverException {
    Preconditions.checkState(!closed);
    closeAllModels();
    changedSinceLastSatQuery = false;
    if (!incremental) {
      for (Expr expr : getAssertedExpressions()) {
        solver.assertFormula(importExpr(expr));
      }
    }

    // Result result;
    /* Shutdown currently not possible TODO: revisit
    try (ShutdownHook hook = new ShutdownHook(shutdownNotifier, solver::interrupt)) {
      shutdownNotifier.shutdownIfNecessary();
      result = solver.checkSat();
    }*/
    Result result = solver.checkSat();
    shutdownNotifier.shutdownIfNecessary();
    return convertSatResult(result);
  }

  private boolean convertSatResult(Result result) throws InterruptedException, SolverException {
    if (result.isSatUnknown()) {
      if (result.getUnknownExplanation().equals(Result.UnknownExplanation.INTERRUPTED)) {
        throw new InterruptedException();
      } else {
        throw new SolverException("CVC4 returned null or unknown on sat check (" + result + ")");
      }
    }
    return result.isUnsat();
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    Preconditions.checkState(!closed);
    checkGenerateUnsatCores();
    Preconditions.checkState(!changedSinceLastSatQuery);
    List<BooleanFormula> converted = new ArrayList<>();
    for (Term aCore : solver.getUnsatCore()) {
      converted.add(creator.encapsulateBoolean(aCore));
    }
    return converted;
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException();
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    throw new UnsupportedOperationException();
  }

  protected Collection<Term> getAssertedExpressions() {
    List<Term> result = new ArrayList<>();
    assertedFormulas.forEach(result::addAll);
    return result;
  }

  @Override
  public void close() {
    if (!closed) {
      closeAllModels();
      assertedFormulas.clear();
      exportMapping.delete();
      // Dont close the solver here, currently we use one solver instance for all stacks + the
      // context!
      // TODO: revisit once i know how to use multiple solvers.
      closed = true;
    }
  }
}
