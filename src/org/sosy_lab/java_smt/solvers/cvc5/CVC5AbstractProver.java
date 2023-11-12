// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import com.google.common.base.Preconditions;
import com.google.common.collect.Collections2;
import com.google.common.collect.ImmutableList;
import io.github.cvc5.CVC5ApiException;
import io.github.cvc5.Result;
import io.github.cvc5.Solver;
import io.github.cvc5.Term;
import io.github.cvc5.UnknownExplanation;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Evaluator;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;

public class CVC5AbstractProver<T> extends AbstractProverWithAllSat<T> {

  private final FormulaManager mgr;
  protected final CVC5FormulaCreator creator;
  protected final Solver solver;
  private boolean changedSinceLastSatQuery = false;

  // TODO: does CVC5 support separation logic in incremental mode?
  protected final boolean incremental;

  protected CVC5AbstractProver(
      CVC5FormulaCreator pFormulaCreator,
      ShutdownNotifier pShutdownNotifier,
      @SuppressWarnings("unused") int randomSeed,
      Set<ProverOptions> pOptions,
      FormulaManager pMgr) {
    super(pOptions, pMgr.getBooleanFormulaManager(), pShutdownNotifier);

    mgr = pMgr;
    creator = pFormulaCreator;
    incremental = !enableSL;
    solver = new Solver();

    setSolverOptions(randomSeed, pOptions, solver);
  }

  protected void setSolverOptions(int randomSeed, Set<ProverOptions> pOptions, Solver pSolver) {
    if (incremental) {
      pSolver.setOption("incremental", "true");
    }
    if (pOptions.contains(ProverOptions.GENERATE_MODELS)) {
      pSolver.setOption("produce-models", "true");
    }
    if (pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE)) {
      pSolver.setOption("produce-unsat-cores", "true");
    }
    pSolver.setOption("produce-assertions", "true");
    pSolver.setOption("dump-models", "true");
    pSolver.setOption("output-language", "smt2");
    pSolver.setOption("seed", String.valueOf(randomSeed));

    // Set Strings option to enable all String features (such as lessOrEquals)
    pSolver.setOption("strings-exp", "true");

    // Enable more complete quantifier solving (for more info see CVC5QuantifiedFormulaManager)
    pSolver.setOption("full-saturate-quant", "true");
  }

  @Override
  protected void pushImpl() throws InterruptedException {
    setChanged();
    if (incremental) {
      try {
        solver.push();
      } catch (CVC5ApiException e) {
        throw new IllegalStateException(
            "You tried to use push() on an CVC5 assertion stack illegally.", e);
      }
    }
  }

  @Override
  protected void popImpl() {
    setChanged();
    if (incremental) {
      try {
        solver.pop();
      } catch (CVC5ApiException e) {
        throw new IllegalStateException(
            "You tried to use pop() on an CVC5 assertion stack illegally.", e);
      }
    }
  }

  @Override
  protected @Nullable T addConstraintImpl(BooleanFormula pF) throws InterruptedException {
    Preconditions.checkState(!closed);
    setChanged();
    Term exp = creator.extractInfo(pF);
    if (incremental) {
      solver.assertFormula(exp);
    }
    return null;
  }

  @SuppressWarnings("resource")
  @Override
  public CVC5Model getModel() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(!changedSinceLastSatQuery);
    checkGenerateModels();
    // special case for CVC5: Models are not permanent and need to be closed
    // before any change is applied to the prover stack. So, we register the Model as Evaluator.
    return registerEvaluator(
        new CVC5Model(
            this,
            mgr,
            creator,
            Collections2.transform(getAssertedFormulas(), creator::extractInfo)));
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
    return registerEvaluator(new CVC5Evaluator(this, creator));
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
    if (!incremental) {
      getAssertedFormulas().forEach(f -> solver.assertFormula(creator.extractInfo(f)));
    }

    /* Shutdown currently not possible in CVC5. */
    Result result = solver.checkSat();
    shutdownNotifier.shutdownIfNecessary();
    return convertSatResult(result);
  }

  private boolean convertSatResult(Result result) throws InterruptedException, SolverException {
    if (result.isUnknown()) {
      if (result.getUnknownExplanation().equals(UnknownExplanation.INTERRUPTED)) {
        throw new InterruptedException();
      } else {
        throw new SolverException(
            "CVC5 returned null or unknown on sat check. Exact result: " + result + ".");
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

  @Override
  public void close() {
    if (!closed) {
      solver.deletePointer();
    }
    super.close();
  }
}
