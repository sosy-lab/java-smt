// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import io.github.cvc5.api.Solver;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;

public final class CVC5SolverContext extends AbstractSolverContext {

  // creator is final, except after closing, then null.
  private CVC5FormulaCreator creator;
  private Solver solver;
  private final ShutdownNotifier shutdownNotifier;
  private final int randomSeed;

  private CVC5SolverContext(
      CVC5FormulaCreator creator,
      CVC5FormulaManager manager,
      ShutdownNotifier pShutdownNotifier,
      Solver solver,
      int pRandomSeed) {
    super(manager);
    this.creator = creator;
    shutdownNotifier = pShutdownNotifier;
    randomSeed = pRandomSeed;
    this.solver = solver;
  }

  // CVC5 loads itself when creating a solver
  @SuppressWarnings({"unused", "resource"})
  public static SolverContext create(
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      int randomSeed,
      NonLinearArithmetic pNonLinearArithmetic,
      FloatingPointRoundingMode pFloatingPointRoundingMode) {

    // Solver is the central class for creating expressions/terms/formulae.
    // Also, creating a solver statically loads CVC5
    Solver newSolver = new Solver();

    // set common options.
    newSolver.setOption("random-seed", String.valueOf(randomSeed));
    newSolver.setOption("produce-models", "true");
    newSolver.setOption("finite-model-find", "true");
    newSolver.setOption("sets-ext", "true");
    newSolver.setOption("output-language", "smtlib2");
    // Set Strings option to enable all String features (such as lessOrEquals)
    newSolver.setOption("strings-exp", "true");

    CVC5FormulaCreator pCreator = new CVC5FormulaCreator(newSolver);

    // Create managers
    CVC5UFManager functionTheory = new CVC5UFManager(pCreator);
    CVC5BooleanFormulaManager booleanTheory = new CVC5BooleanFormulaManager(pCreator);
    CVC5IntegerFormulaManager integerTheory =
        new CVC5IntegerFormulaManager(pCreator, pNonLinearArithmetic);
    CVC5RationalFormulaManager rationalTheory =
        new CVC5RationalFormulaManager(pCreator, pNonLinearArithmetic);
    CVC5BitvectorFormulaManager bitvectorTheory =
        new CVC5BitvectorFormulaManager(pCreator, booleanTheory);

    CVC5FloatingPointFormulaManager fpTheory =
        new CVC5FloatingPointFormulaManager(pCreator, pFloatingPointRoundingMode);

    CVC5QuantifiedFormulaManager qfTheory = new CVC5QuantifiedFormulaManager(pCreator);

    CVC5ArrayFormulaManager arrayTheory = new CVC5ArrayFormulaManager(pCreator);
    CVC5SLFormulaManager slTheory = new CVC5SLFormulaManager(pCreator);
    CVC5StringFormulaManager strTheory = new CVC5StringFormulaManager(pCreator);
    CVC5FormulaManager manager =
        new CVC5FormulaManager(
            pCreator,
            functionTheory,
            booleanTheory,
            integerTheory,
            rationalTheory,
            bitvectorTheory,
            fpTheory,
            qfTheory,
            arrayTheory,
            slTheory,
            strTheory);

    return new CVC5SolverContext(pCreator, manager, pShutdownNotifier, newSolver, randomSeed);
  }

  @Override
  public String getVersion() {
    // TODO: Check if this is correct or if there is no version info.
    return "CVC5 " + solver.toString();
  }

  @Override
  public void close() {
    if (creator != null) {
      solver.close();
      creator = null;
    }
  }

  @Override
  public Solvers getSolverName() {
    return Solvers.CVC5;
  }

  @Override
  public ProverEnvironment newProverEnvironment0(Set<ProverOptions> pOptions) {
    return new CVC5TheoremProver(
        creator,
        shutdownNotifier,
        randomSeed,
        pOptions,
        getFormulaManager().getBooleanFormulaManager(),
        solver);
  }

  @Override
  protected boolean supportsAssumptionSolving() {
    return false;
  }

  @Override
  protected InterpolatingProverEnvironment<?> newProverEnvironmentWithInterpolation0(
      Set<ProverOptions> pSet) {
    // FIXME
    return null;
  }

  @Override
  protected OptimizationProverEnvironment newOptimizationProverEnvironment0(
      Set<ProverOptions> pSet) {
    throw new UnsupportedOperationException("CVC4 does not support optimization");
  }
}
