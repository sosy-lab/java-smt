// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import ap.api.SimpleAPI;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

public final class PrincessSolverContext extends AbstractSolverContext {

  private final PrincessFormulaManager manager;
  private final PrincessFormulaCreator creator;
  private final boolean useBinary;

  private PrincessSolverContext(
      PrincessFormulaManager manager, PrincessFormulaCreator creator, boolean useBinary) {
    super(manager);
    this.manager = manager;
    this.creator = creator;
    this.useBinary = useBinary;
  }

  public static SolverContext create(
      Configuration config,
      boolean useBinary,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate pLogfileTemplate,
      int pRandomSeed,
      NonLinearArithmetic pNonLinearArithmetic)
      throws InvalidConfigurationException {
    PrincessEnvironment env =
        new PrincessEnvironment(config, pLogfileTemplate, pShutdownNotifier, pRandomSeed);
    PrincessFormulaCreator creator = new PrincessFormulaCreator(env);

    // Create managers
    PrincessUFManager functionTheory = new PrincessUFManager(creator);
    PrincessBooleanFormulaManager booleanTheory = new PrincessBooleanFormulaManager(creator);
    PrincessIntegerFormulaManager integerTheory =
        new PrincessIntegerFormulaManager(creator, pNonLinearArithmetic);
    PrincessBitvectorFormulaManager bitvectorTheory =
        new PrincessBitvectorFormulaManager(creator, booleanTheory);
    PrincessArrayFormulaManager arrayTheory = new PrincessArrayFormulaManager(creator);
    PrincessQuantifiedFormulaManager quantifierTheory =
        new PrincessQuantifiedFormulaManager(creator);
    PrincessFormulaManager manager =
        new PrincessFormulaManager(
            creator,
            functionTheory,
            booleanTheory,
            integerTheory,
            bitvectorTheory,
            arrayTheory,
            quantifierTheory);
    return new PrincessSolverContext(manager, creator, useBinary);
  }

  @SuppressWarnings("resource")
  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> options) {
    if (options.contains(ProverOptions.GENERATE_UNSAT_CORE_OVER_ASSUMPTIONS)) {
      throw new UnsupportedOperationException(
          "Princess does not support unsat core generation with assumptions yet");
    }
    if (useBinary) {
      options.add(ProverOptions.USE_BINARY);
    }
    return (PrincessTheoremProver) creator.getEnv().getNewProver(false, manager, creator, options);
  }

  @SuppressWarnings("resource")
  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> options) {
    if (useBinary) {
      options.add(ProverOptions.USE_BINARY);
    }
    return (PrincessInterpolatingProver)
        creator.getEnv().getNewProver(true, manager, creator, options);
  }

  @Override
  public OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> options) {
    throw new UnsupportedOperationException("Princess does not support optimization");
  }

  @Override
  public String getVersion() {
    return "Princess " + SimpleAPI.version();
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.PRINCESS;
  }

  @Override
  public void close() {
    creator.getEnv().close();
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }
}
