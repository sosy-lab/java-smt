// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractProverWithAllSat;
import org.sosy_lab.java_smt.basicimpl.CachingModel;

final class LeanSmtTheoremProver extends AbstractProverWithAllSat<Void> implements ProverEnvironment {

  private final LeanSmtFormulaCreator creator;
  private final String logic;

  private static final class SnapshotSymbols {
    private final Set<String> variables;
    private final Set<String> ufs;

    private SnapshotSymbols(Set<String> pVariables, Set<String> pUfs) {
      variables = ImmutableSet.copyOf(pVariables);
      ufs = ImmutableSet.copyOf(pUfs);
    }
  }

  LeanSmtTheoremProver(
      LeanSmtFormulaCreator pCreator,
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr,
      ShutdownNotifier pShutdownNotifier,
      String pLogic) {
    super(pOptions, pBmgr, pShutdownNotifier);
    creator = pCreator;
    logic = pLogic;
  }

  @Override
  protected boolean hasPersistentModel() {
    return true;
  }

  @Override
  protected void popImpl() {
    // JavaSMT keeps the assertion stack. LeanSMT sees only fresh snapshots.
  }

  @Override
  protected @Nullable Void addConstraintImpl(BooleanFormula pConstraint) {
    // JavaSMT keeps the active constraints. LeanSMT sees only fresh snapshots.
    return null;
  }

  @Override
  protected void pushImpl() {
    // JavaSMT keeps the assertion stack. LeanSMT sees only fresh snapshots.
  }

  @Override
  protected boolean isUnsatImpl() throws SolverException, InterruptedException {
    int result = checkSatOnSnapshot();
    if (result == LeanSMTConstants.LEANSMT_UNSAT) {
      return true;
    } else if (result == LeanSMTConstants.LEANSMT_SAT) {
      return false;
    }
    throwOnUnknownOrUnexpectedResult(
        result == LeanSMTConstants.LEANSMT_UNKNOWN, result, "satisfiability check");
    throw new AssertionError("unreachable");
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException(ASSUMPTION_SOLVING_NOT_SUPPORTED);
  }

  static void throwOnUnknownOrUnexpectedResult(
      boolean isUnknownResult, int result, String operationDescription)
      throws SolverException {
    if (isUnknownResult) {
      throw new SolverException("LeanSMT returned UNKNOWN for " + operationDescription);
    }
    throw new SolverException("Unexpected LeanSMT satisfiability result: " + result);
  }

  @Override
  public Model getModel() throws SolverException {
    checkGenerateModels();
    return new CachingModel(getEvaluatorWithoutChecks());
  }

  @Override
  protected LeanSmtModel getEvaluatorWithoutChecks() throws SolverException {
    SnapshotSymbols snapshotSymbols = collectSnapshotSymbols();
    long modelSolver = createSatModelSnapshotSolver(snapshotSymbols);
    try {
      return registerEvaluator(
          new LeanSmtModel(
              this,
              creator,
              modelSolver,
              getRelevantModelHandles()));
    } catch (RuntimeException e) {
      LeanSmtNativeApi.deleteSolverAsync(modelSolver);
      throw e;
    }
  }

  @Override
  public List<BooleanFormula> getUnsatCore() {
    throw new UnsupportedOperationException(UNSAT_CORE_NOT_SUPPORTED);
  }

  @Override
  public Optional<List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    Preconditions.checkNotNull(pAssumptions);
    throw new UnsupportedOperationException(UNSAT_CORE_NOT_SUPPORTED);
  }

  private Set<Long> getRelevantModelHandles() {
    ImmutableSet.Builder<Long> relevant = ImmutableSet.builder();
    Set<Long> visited = new HashSet<>();
    for (BooleanFormula constraint : getAssertedFormulas()) {
      collectRelevantModelHandles(creator.extractInfoFromFormula(constraint), visited, relevant);
    }
    return relevant.build();
  }

  private void collectRelevantModelHandles(
      long handle, Set<Long> visited, ImmutableSet.Builder<Long> relevant) {
    if (!visited.add(handle)) {
      return;
    }
    relevant.add(handle);
    LeanSmtFormulaCreator.Expr expr = creator.getExpression(handle);
    for (long arg : expr.arguments) {
      collectRelevantModelHandles(arg, visited, relevant);
    }
  }

  private long createEmptySolver() throws SolverException {
    long solver = LeanSmtNativeApi.createSolverCvc5();
    LeanSmtNativeApi.setLogic(solver, logic);
    return solver;
  }

  private void assertAllConstraints(long solver) throws SolverException, InterruptedException {
    for (BooleanFormula constraint : getAssertedFormulas()) {
      shutdownNotifier.shutdownIfNecessary();
      LeanSmtNativeApi.assertTerm(solver, creator.extractInfoFromFormula(constraint));
    }
  }

  private int checkSatOnSnapshot() throws SolverException, InterruptedException {
    long solver = createSolverSnapshot(collectSnapshotSymbols());
    try {
      return LeanSmtNativeApi.checkSat(solver);
    } finally {
      LeanSmtNativeApi.deleteSolverAsync(solver);
    }
  }

  private long createSolverSnapshot(SnapshotSymbols snapshotSymbols)
      throws SolverException, InterruptedException {
    long solver = createEmptySolver();
    boolean success = false;
    try {
      declareSnapshotSymbols(solver, snapshotSymbols);
      assertAllConstraints(solver);
      success = true;
      return solver;
    } finally {
      if (!success) {
        LeanSmtNativeApi.deleteSolverAsync(solver);
      }
    }
  }

  private SnapshotSymbols collectSnapshotSymbols() {
    Set<String> referencedVariables = new HashSet<>();
    Set<String> referencedUfs = new HashSet<>();
    Set<Long> visited = new HashSet<>();
    for (BooleanFormula constraint : getAssertedFormulas()) {
      collectReferencedSymbols(
          creator.extractInfoFromFormula(constraint), visited, referencedVariables, referencedUfs);
    }
    return new SnapshotSymbols(referencedVariables, referencedUfs);
  }

  private void declareSnapshotSymbols(long solver, SnapshotSymbols snapshotSymbols)
      throws SolverException {
    creator.redeclareVariables(solver, snapshotSymbols.variables);
    creator.redeclareUfDeclarations(solver, snapshotSymbols.ufs);
  }

  private void collectReferencedSymbols(
      long handle,
      Set<Long> visited,
      Set<String> referencedVariables,
      Set<String> referencedUfs) {
    if (!visited.add(handle)) {
      return;
    }
    LeanSmtFormulaCreator.Expr expr = creator.getExpression(handle);
    if (expr.kind == LeanSmtFormulaCreator.ExprKind.VARIABLE) {
      referencedVariables.add(expr.symbol);
    } else if (expr.declarationKind == org.sosy_lab.java_smt.api.FunctionDeclarationKind.UF) {
      referencedUfs.add(expr.symbol);
    }
    for (long arg : expr.arguments) {
      collectReferencedSymbols(arg, visited, referencedVariables, referencedUfs);
    }
  }

  private long createSatModelSnapshotSolver(SnapshotSymbols snapshotSymbols) throws SolverException {
    long solver = 0L;
    boolean success = false;
    try {
      solver = createSolverSnapshot(snapshotSymbols);
      int result = LeanSmtNativeApi.checkSat(solver);
      if (result == LeanSMTConstants.LEANSMT_SAT) {
        success = true;
        return solver;
      }
      if (result == LeanSMTConstants.LEANSMT_UNSAT) {
        throw new SolverException("Expected SAT while constructing LeanSMT model snapshot");
      }
      throwOnUnknownOrUnexpectedResult(
          result == LeanSMTConstants.LEANSMT_UNKNOWN, result, "LeanSMT model snapshot");
      throw new AssertionError("unreachable");
    } catch (InterruptedException e) {
      Thread.currentThread().interrupt();
      throw new SolverException("Interrupted while constructing LeanSMT model snapshot", e);
    } finally {
      if (!success && solver != 0L) {
        LeanSmtNativeApi.deleteSolverAsync(solver);
      }
    }
  }
}
