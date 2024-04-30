// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.dreal4;

import java.util.Set;
import java.util.function.Consumer;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Config;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.DrealJNI;

public class DReal4SolverContext extends AbstractSolverContext {

  private final DReal4FormulaManager manager;
  private final DReal4FormulaCreator creator;
  private final ShutdownNotifier shutdownNotifier;

  public DReal4SolverContext(
      DReal4FormulaManager pManager,
      DReal4FormulaCreator pCreator,
      ShutdownNotifier pShutdownNotifier) {
    super(pManager);
    manager = pManager;
    creator = pCreator;
    shutdownNotifier = pShutdownNotifier;
  }

  public static DReal4SolverContext create(
      ShutdownNotifier pShutdownNotifier,
      int randomSeed,
      NonLinearArithmetic pNonLinearArithmetic,
      Consumer<String> pLoader) {

    pLoader.accept("drealjava");

    // Create config
    Config config = new Config();
    config.mutableRandomSeed(randomSeed);

    DReal4FormulaCreator creator = new DReal4FormulaCreator(config);

    // Create manager
    DReal4UFManager functionTheory = new DReal4UFManager(creator);
    DReal4BooleanFormulaManager booleanTheory = new DReal4BooleanFormulaManager(creator);
    DReal4IntegerFormulaManager integerTheory =
        new DReal4IntegerFormulaManager(creator, pNonLinearArithmetic);
    DReal4RationalFormulaManager rationalTheory =
        new DReal4RationalFormulaManager(creator, pNonLinearArithmetic);
    DReal4QuantifiedFormulaManager quantifierTheory = new DReal4QuantifiedFormulaManager(creator);
    DReal4FormulaManager manager =
        new DReal4FormulaManager(
            creator,
            functionTheory,
            booleanTheory,
            integerTheory,
            rationalTheory,
            quantifierTheory);
    return new DReal4SolverContext(manager, creator, pShutdownNotifier);
  }

  @Override
  public String getVersion() {
    return "dReal " + DrealJNI.contextVersion();
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.DREAL4;
  }

  @Override
  public void close() {}

  @Override
  protected ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    return new DReal4TheoremProver(creator, pOptions, manager, shutdownNotifier);
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("dReal does not support interpolation.");
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("dReal does not support optimization.");
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }
}
