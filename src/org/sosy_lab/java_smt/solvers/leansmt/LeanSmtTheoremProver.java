// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashSet;
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
  private long currentSolver = 0L;
  private @Nullable ImmutableList<BooleanFormula> lastSatAssumptions = null;
  private boolean rebuildRequired = false;
  private final Set<String> declaredVariablesInCurrentSolver = new HashSet<>();
  private final Set<Long> assertedUfConstraintsInCurrentSolver = new HashSet<>();
  private final Set<Long> assertedFloorConstraintsInCurrentSolver = new HashSet<>();
  private final Set<Long> assertedIntToBvConstraintsInCurrentSolver = new HashSet<>();
  private final Set<Long> assertedRationalConstConstraintsInCurrentSolver = new HashSet<>();
  // Assertion order invariant:
  // 1) declare/redeclare symbols
  // 2) assert derived constraints (UF congruence, floor, constrained rationals)
  // 3) assert user constraints / assumptions
  // This keeps rebuilt and incremental paths semantically aligned.

  LeanSmtTheoremProver(
      LeanSmtFormulaCreator pCreator,
      Set<ProverOptions> pOptions,
      BooleanFormulaManager pBmgr,
      ShutdownNotifier pShutdownNotifier,
      String pLogic) {
    super(pOptions, pBmgr, pShutdownNotifier);
    creator = pCreator;
    logic = pLogic;
    try {
      currentSolver = createFreshCurrentSolver();
    } catch (SolverException e) {
      throw new IllegalStateException("Failed to initialize LeanSMT prover solver", e);
    }
  }

  @Override
  protected boolean hasPersistentModel() {
    return true;
  }

  @Override
  protected void popImpl() {
    // LeanSMT currently has no native push/pop support.
    // Mark solver dirty and lazily rebuild from asserted formulas on demand.
    rebuildRequired = true;
    lastSatAssumptions = null;
  }

  @Override
  protected @Nullable Void addConstraintImpl(BooleanFormula pConstraint) {
    if (!rebuildRequired) {
      try {
        // Variables can be introduced after prover creation; declare only new ones.
        creator.redeclareMissingVariables(currentSolver, declaredVariablesInCurrentSolver);
        assertPendingDerivedConstraints();
        LeanSmtNativeApi.assertTerm(currentSolver, creator.extractInfoFromFormula(pConstraint));
      } catch (SolverException e) {
        // Keep going and rebuild lazily in the next check-sat.
        rebuildRequired = true;
      }
    }
    lastSatAssumptions = null;
    return null;
  }

  @Override
  protected void pushImpl() {
    // LeanSMT currently has no native push/pop support.
    // No native action needed here.
  }

  @Override
  protected boolean isUnsatImpl() throws SolverException, InterruptedException {
    ensureUpToDateSolver();
    assertPendingDerivedConstraints();
    int result = LeanSmtNativeApi.checkSat(currentSolver);
    if (result == LeanSMTConstants.LEANSMT_UNSAT) {
      lastSatAssumptions = null;
      return true;
    } else if (result == LeanSMTConstants.LEANSMT_SAT) {
      lastSatAssumptions = ImmutableList.of();
      return false;
    }
    lastSatAssumptions = null;
    throwOnUnknownOrUnexpectedResult(
        result == LeanSMTConstants.LEANSMT_UNKNOWN, result, "satisfiability check");
    throw new AssertionError("unreachable");
  }

  @Override
  public boolean isUnsatWithAssumptions(Collection<BooleanFormula> pAssumptions)
      throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    changedSinceLastSatQuery = false;
    ensureUpToDateSolver();

    ImmutableList<BooleanFormula> assumptions =
        ImmutableList.copyOf(new LinkedHashSet<>(pAssumptions));
    int result;
    if (assumptions.isEmpty()) {
      assertPendingDerivedConstraints();
      result = LeanSmtNativeApi.checkSat(currentSolver);
    } else {
      // Assumptions are checked on a temporary solver to preserve the base incremental solver
      // state, matching JavaSMT assumption semantics.
      long tmpSolver = createTemporarySolver();
      try {
        assertAllDerivedConstraints(tmpSolver);
        for (BooleanFormula constraint : getAssertedFormulas()) {
          shutdownNotifier.shutdownIfNecessary();
          LeanSmtNativeApi.assertTerm(tmpSolver, creator.extractInfoFromFormula(constraint));
        }
        for (BooleanFormula assumption : assumptions) {
          shutdownNotifier.shutdownIfNecessary();
          LeanSmtNativeApi.assertTerm(tmpSolver, creator.extractInfoFromFormula(assumption));
        }
        result = LeanSmtNativeApi.checkSat(tmpSolver);
      } finally {
        LeanSmtNativeApi.deleteSolverAsync(tmpSolver);
      }
    }

    if (result == LeanSMTConstants.LEANSMT_UNSAT) {
      lastSatAssumptions = null;
      return true;
    } else if (result == LeanSMTConstants.LEANSMT_SAT) {
      lastSatAssumptions = assumptions;
      return false;
    }
    lastSatAssumptions = null;
    throwOnUnknownOrUnexpectedResult(
        result == LeanSMTConstants.LEANSMT_UNKNOWN, result, "satisfiability check with assumptions");
    throw new AssertionError("unreachable");
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
    ImmutableList<BooleanFormula> assumptions =
        Preconditions.checkNotNull(lastSatAssumptions, "No satisfying LeanSMT state available");
    long modelSolver = createModelSnapshotSolver(assumptions);
    try {
      return registerEvaluator(
          new LeanSmtModel(
              this, creator, modelSolver, getRelevantModelHandles(assumptions), true));
    } catch (SolverException | RuntimeException e) {
      LeanSmtNativeApi.deleteSolverAsync(modelSolver);
      throw e;
    }
  }

  @Override
  public java.util.List<BooleanFormula> getUnsatCore() {
    checkGenerateUnsatCores();
    try {
      return computeUnsatCore(
          ImmutableList.of(),
          getAssertedFormulas(),
          "assertions for unsat core extraction");
    } catch (InterruptedException e) {
      Thread.currentThread().interrupt();
      throw new IllegalStateException("Interrupted during LeanSMT unsat-core extraction", e);
    } catch (SolverException e) {
      throw new IllegalStateException("LeanSMT unsat-core extraction failed", e);
    }
  }

  @Override
  public Optional<java.util.List<BooleanFormula>> unsatCoreOverAssumptions(
      Collection<BooleanFormula> pAssumptions) throws SolverException, InterruptedException {
    Preconditions.checkNotNull(pAssumptions);
    checkGenerateUnsatCoresOverAssumptions();

    if (!isUnsatWithAssumptions(pAssumptions)) {
      return Optional.empty();
    }

    // Keep deterministic order while avoiding duplicate work.
    List<BooleanFormula> assumptions = ImmutableList.copyOf(new LinkedHashSet<>(pAssumptions));
    return Optional.of(
        computeUnsatCore(getAssertedFormulas(), assumptions, "assumptions for unsat core"));
  }

  @Override
  public void close() {
    if (!closed) {
      if (currentSolver != 0L) {
        LeanSmtNativeApi.deleteSolverAsync(currentSolver);
      }
      currentSolver = 0L;
    }
    super.close();
  }

  private long createFreshCurrentSolver() throws SolverException {
    long solver = LeanSmtNativeApi.createSolverCvc5();
    LeanSmtNativeApi.setLogic(solver, logic);
    declaredVariablesInCurrentSolver.clear();
    assertedUfConstraintsInCurrentSolver.clear();
    assertedFloorConstraintsInCurrentSolver.clear();
    assertedIntToBvConstraintsInCurrentSolver.clear();
    assertedRationalConstConstraintsInCurrentSolver.clear();
    creator.redeclareMissingVariables(solver, declaredVariablesInCurrentSolver);
    return solver;
  }

  private Set<Long> getRelevantModelHandles(Collection<BooleanFormula> assumptions) {
    ImmutableSet.Builder<Long> relevant = ImmutableSet.builder();
    Set<Long> visited = new HashSet<>();
    for (BooleanFormula constraint : getAssertedFormulas()) {
      collectRelevantModelHandles(creator.extractInfoFromFormula(constraint), visited, relevant);
    }
    for (BooleanFormula assumption : assumptions) {
      collectRelevantModelHandles(creator.extractInfoFromFormula(assumption), visited, relevant);
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

  /**
   * Create a temporary solver with the current variable declarations.
   *
   * <p>Temporary solver creation must not mutate tracking structures used by the incremental base
   * solver.
   */
  private long createTemporarySolver() throws SolverException {
    long solver = LeanSmtNativeApi.createSolverCvc5();
    LeanSmtNativeApi.setLogic(solver, logic);
    Set<String> declaredVariablesInTemporarySolver = new HashSet<>();
    creator.redeclareMissingVariables(solver, declaredVariablesInTemporarySolver);
    return solver;
  }

  private void ensureUpToDateSolver() throws SolverException, InterruptedException {
    if (!rebuildRequired) {
      return;
    }
    shutdownNotifier.shutdownIfNecessary();
    if (currentSolver != 0L) {
      LeanSmtNativeApi.deleteSolverAsync(currentSolver);
    }

    currentSolver = createFreshCurrentSolver();
    assertPendingDerivedConstraints();
    for (BooleanFormula constraint : getAssertedFormulas()) {
      shutdownNotifier.shutdownIfNecessary();
      LeanSmtNativeApi.assertTerm(currentSolver, creator.extractInfoFromFormula(constraint));
    }
    rebuildRequired = false;
    lastSatAssumptions = null;
  }

  private void assertPendingDerivedConstraints() throws SolverException {
    for (Long c : creator.getUfCongruenceConstraints()) {
      if (assertedUfConstraintsInCurrentSolver.add(c)) {
        LeanSmtNativeApi.assertTerm(currentSolver, c);
      }
    }
    for (Long c : creator.getFloorConstraints()) {
      if (assertedFloorConstraintsInCurrentSolver.add(c)) {
        LeanSmtNativeApi.assertTerm(currentSolver, c);
      }
    }
    for (Long c : creator.getIntToBvConstraints()) {
      if (assertedIntToBvConstraintsInCurrentSolver.add(c)) {
        LeanSmtNativeApi.assertTerm(currentSolver, c);
      }
    }
    for (Long c : creator.getRationalConstantConstraints()) {
      if (assertedRationalConstConstraintsInCurrentSolver.add(c)) {
        LeanSmtNativeApi.assertTerm(currentSolver, c);
      }
    }
  }

  private void assertAllDerivedConstraints(long solver) throws SolverException, InterruptedException {
    for (Long ufConstraint : creator.getUfCongruenceConstraints()) {
      shutdownNotifier.shutdownIfNecessary();
      LeanSmtNativeApi.assertTerm(solver, ufConstraint);
    }
    for (Long floorConstraint : creator.getFloorConstraints()) {
      shutdownNotifier.shutdownIfNecessary();
      LeanSmtNativeApi.assertTerm(solver, floorConstraint);
    }
    for (Long intToBvConstraint : creator.getIntToBvConstraints()) {
      shutdownNotifier.shutdownIfNecessary();
      LeanSmtNativeApi.assertTerm(solver, intToBvConstraint);
    }
    for (Long rationalConstantConstraint : creator.getRationalConstantConstraints()) {
      shutdownNotifier.shutdownIfNecessary();
      LeanSmtNativeApi.assertTerm(solver, rationalConstantConstraint);
    }
  }

  /**
   * Compute an unsat core by deletion-based minimization.
   *
   * <p>This is intentionally solver-agnostic: LeanSMT currently does not expose a native unsat-core
   * API through the JNI wrapper, so we derive a core by repeated SAT checks on temporary solvers.
   */
  private List<BooleanFormula> computeUnsatCore(
      Collection<BooleanFormula> fixedConstraints,
      Collection<BooleanFormula> candidates,
      String contextDescription)
      throws SolverException, InterruptedException {
    List<BooleanFormula> core = new java.util.ArrayList<>(new LinkedHashSet<>(candidates));

    int initial = checkSatOnTemporarySolver(fixedConstraints, core);
    if (initial != LeanSMTConstants.LEANSMT_UNSAT) {
      throw new SolverException(
          "Expected UNSAT while extracting LeanSMT core from "
              + contextDescription
              + ", but got result "
              + initial);
    }

    for (int i = 0; i < core.size(); ) {
      BooleanFormula removed = core.remove(i);
      int result = checkSatOnTemporarySolver(fixedConstraints, core);

      if (result == LeanSMTConstants.LEANSMT_UNSAT) {
        // Constraint/assumption is redundant for UNSAT and stays removed.
        // Keep index unchanged because the next candidate shifted into the same position.
      } else if (result == LeanSMTConstants.LEANSMT_SAT) {
        core.add(i, removed);
        i++;
      } else if (result == LeanSMTConstants.LEANSMT_UNKNOWN) {
        throw new SolverException(
            "LeanSMT returned UNKNOWN while extracting unsat core from " + contextDescription);
      } else {
        throw new SolverException(
            "Unexpected LeanSMT satisfiability result during unsat-core extraction: " + result);
      }
    }
    return core;
  }

  private int checkSatOnTemporarySolver(
      Collection<BooleanFormula> fixedConstraints, Collection<BooleanFormula> extraConstraints)
      throws SolverException, InterruptedException {
    long tmpSolver = createTemporarySolver();
    try {
      assertAllDerivedConstraints(tmpSolver);

      for (BooleanFormula constraint : fixedConstraints) {
        shutdownNotifier.shutdownIfNecessary();
        LeanSmtNativeApi.assertTerm(tmpSolver, creator.extractInfoFromFormula(constraint));
      }
      for (BooleanFormula constraint : extraConstraints) {
        shutdownNotifier.shutdownIfNecessary();
        LeanSmtNativeApi.assertTerm(tmpSolver, creator.extractInfoFromFormula(constraint));
      }
      return LeanSmtNativeApi.checkSat(tmpSolver);
    } finally {
      LeanSmtNativeApi.deleteSolverAsync(tmpSolver);
    }
  }

  private long createModelSnapshotSolver(Collection<BooleanFormula> assumptions)
      throws SolverException {
    long tmpSolver = createTemporarySolver();
    boolean success = false;
    try {
      assertAllDerivedConstraints(tmpSolver);
      for (BooleanFormula constraint : getAssertedFormulas()) {
        shutdownNotifier.shutdownIfNecessary();
        LeanSmtNativeApi.assertTerm(tmpSolver, creator.extractInfoFromFormula(constraint));
      }
      for (BooleanFormula assumption : assumptions) {
        shutdownNotifier.shutdownIfNecessary();
        LeanSmtNativeApi.assertTerm(tmpSolver, creator.extractInfoFromFormula(assumption));
      }

      int result = LeanSmtNativeApi.checkSat(tmpSolver);
      if (result != LeanSMTConstants.LEANSMT_SAT) {
        if (result == LeanSMTConstants.LEANSMT_UNSAT) {
          throw new SolverException("Expected SAT while constructing LeanSMT model snapshot");
        }
        throwOnUnknownOrUnexpectedResult(
            result == LeanSMTConstants.LEANSMT_UNKNOWN, result, "LeanSMT model snapshot");
      }

      success = true;
      return tmpSolver;
    } catch (InterruptedException e) {
      Thread.currentThread().interrupt();
      throw new SolverException("Interrupted while constructing LeanSMT model snapshot", e);
    } finally {
      if (!success) {
        LeanSmtNativeApi.deleteSolverAsync(tmpSolver);
      }
    }
  }
}
