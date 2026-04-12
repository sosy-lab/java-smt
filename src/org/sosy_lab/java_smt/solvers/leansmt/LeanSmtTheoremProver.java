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

  private static final class SnapshotPlan {
    private final ImmutableSet<BooleanFormula> constraints;
    private final Set<String> variables;
    private final Set<String> ufs;
    private final Set<Long> relevantModelHandles;

    private SnapshotPlan(
        ImmutableSet<BooleanFormula> pConstraints,
        Set<String> pVariables,
        Set<String> pUfs,
        Set<Long> pRelevantModelHandles) {
      constraints = pConstraints;
      variables = ImmutableSet.copyOf(pVariables);
      ufs = ImmutableSet.copyOf(pUfs);
      relevantModelHandles = ImmutableSet.copyOf(pRelevantModelHandles);
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
    // JavaSMT owns the assertion stack; LeanSMT only sees snapshot solves.
  }

  @Override
  protected @Nullable Void addConstraintImpl(BooleanFormula pConstraint) {
    // JavaSMT owns the active constraints; LeanSMT only sees snapshot solves.
    return null;
  }

  @Override
  protected void pushImpl() {
    // JavaSMT owns the assertion stack; LeanSMT only sees snapshot solves.
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
    SnapshotPlan snapshotPlan = collectSnapshotPlan(true);
    long modelSolver = createSatModelSnapshotSolver(snapshotPlan);
    try {
      return registerEvaluator(
          new LeanSmtModel(this, creator, modelSolver, snapshotPlan.relevantModelHandles));
    } catch (RuntimeException e) {
      LeanSmtNativeApi.deleteSolverBestEffort(modelSolver);
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

  private long createEmptySolver() throws SolverException {
    long solver = LeanSmtNativeApi.createSolverCvc5();
    LeanSmtNativeApi.setLogic(solver, logic);
    return solver;
  }

  private void assertAllConstraints(long solver, SnapshotPlan snapshotPlan)
      throws SolverException, InterruptedException {
    for (BooleanFormula constraint : snapshotPlan.constraints) {
      shutdownNotifier.shutdownIfNecessary();
      LeanSmtNativeApi.assertTerm(solver, creator.extractInfoFromFormula(constraint));
    }
  }

  private int checkSatOnSnapshot() throws SolverException, InterruptedException {
    long solver = createSolverSnapshot(collectSnapshotPlan(false));
    try {
      return LeanSmtNativeApi.checkSat(solver);
    } finally {
      LeanSmtNativeApi.deleteSolverBestEffort(solver);
    }
  }

  private long createSolverSnapshot(SnapshotPlan snapshotPlan)
      throws SolverException, InterruptedException {
    long solver = createEmptySolver();
    boolean success = false;
    try {
      creator.redeclareVariables(solver, snapshotPlan.variables);
      creator.redeclareUfDeclarations(solver, snapshotPlan.ufs);
      assertAllConstraints(solver, snapshotPlan);
      success = true;
      return solver;
    } finally {
      if (!success) {
        LeanSmtNativeApi.deleteSolverBestEffort(solver);
      }
    }
  }

  private SnapshotPlan collectSnapshotPlan(boolean collectRelevantModelHandles) {
    ImmutableSet<BooleanFormula> constraints = getAssertedFormulas();
    Set<String> referencedVariables = new HashSet<>();
    Set<String> referencedUfs = new HashSet<>();
    ImmutableSet.Builder<Long> relevantHandles =
        collectRelevantModelHandles ? ImmutableSet.builder() : null;
    Set<Long> visited = new HashSet<>();
    for (BooleanFormula constraint : constraints) {
      collectSnapshotMetadata(
          creator.extractInfoFromFormula(constraint),
          visited,
          referencedVariables,
          referencedUfs,
          relevantHandles);
    }
    return new SnapshotPlan(
        constraints,
        referencedVariables,
        referencedUfs,
        relevantHandles == null ? ImmutableSet.of() : relevantHandles.build());
  }

  private void collectSnapshotMetadata(
      long handle,
      Set<Long> visited,
      Set<String> referencedVariables,
      Set<String> referencedUfs,
      ImmutableSet.Builder<Long> relevantHandles) {
    if (!visited.add(handle)) {
      return;
    }
    if (relevantHandles != null) {
      relevantHandles.add(handle);
    }
    LeanSmtFormulaCreator.Expr expr = creator.getExpression(handle);
    if (expr.kind == LeanSmtFormulaCreator.ExprKind.VARIABLE) {
      referencedVariables.add(expr.symbol);
    } else if (expr.declarationKind == org.sosy_lab.java_smt.api.FunctionDeclarationKind.UF) {
      referencedUfs.add(expr.symbol);
    }
    for (long arg : expr.arguments) {
      collectSnapshotMetadata(arg, visited, referencedVariables, referencedUfs, relevantHandles);
    }
  }

  private long createSatModelSnapshotSolver(SnapshotPlan snapshotPlan) throws SolverException {
    long solver = 0L;
    boolean success = false;
    try {
      solver = createSolverSnapshot(snapshotPlan);
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
        LeanSmtNativeApi.deleteSolverBestEffort(solver);
      }
    }
  }
}
