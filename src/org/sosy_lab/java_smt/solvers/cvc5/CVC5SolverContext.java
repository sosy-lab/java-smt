// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import edu.stanford.CVC4.Configuration;
import io.github.cvc5.api.Solver;
import java.util.Set;
import java.util.function.Consumer;
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
      int pRandomSeed) {
    super(manager);
    this.creator = creator;
    shutdownNotifier = pShutdownNotifier;
    randomSeed = pRandomSeed;
  }

  public static SolverContext create(
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      int randomSeed,
      NonLinearArithmetic pNonLinearArithmetic,
      FloatingPointRoundingMode pFloatingPointRoundingMode,
      Consumer<String> pLoader) {

    // Solver is the central class for creating expressions/terms/formulae.
    solver = new Solver();
    CVC5FormulaCreator creator = new CVC5FormulaCreator(solver);

    // set common options.
    solver.setOption("random-seed", String.valueOf(randomSeed));
    solver.setOption("produce-models", "true");
    solver.setOption("finite-model-find", "true");
    solver.setOption("sets-ext", "true");
    solver.setOption("output-language", "smtlib2");
    // Set Strings option to enable all String features (such as lessOrEquals)
    solver.setOption("strings-exp", "true");

    // Create managers
    CVC5UFManager functionTheory = new CVC5UFManager(creator);
    CVC5BooleanFormulaManager booleanTheory = new CVC5BooleanFormulaManager(creator);
    CVC5IntegerFormulaManager integerTheory =
        new CVC5IntegerFormulaManager(creator, pNonLinearArithmetic);
    CVC5RationalFormulaManager rationalTheory =
        new CVC5RationalFormulaManager(creator, pNonLinearArithmetic);
    CVC5BitvectorFormulaManager bitvectorTheory =
        new CVC5BitvectorFormulaManager(creator, booleanTheory);

    CVC5FloatingPointFormulaManager fpTheory;
    if (Configuration.isBuiltWithSymFPU()) {
      fpTheory = new CVC5FloatingPointFormulaManager(creator, pFloatingPointRoundingMode);
    } else {
      fpTheory = null;
      // TODO: is this config check needed?
    }

    CVC5QuantifiedFormulaManager qfTheory = new CVC5QuantifiedFormulaManager(creator);

    CVC5ArrayFormulaManager arrayTheory = new CVC5ArrayFormulaManager(creator);
    CVC5SLFormulaManager slTheory = new CVC5SLFormulaManager(creator);
    CVC5StringFormulaManager strTheory = new CVC5StringFormulaManager(creator);
    CVC5FormulaManager manager =
        new CVC5FormulaManager(
            creator,
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

    return new CVC5SolverContext(creator, manager, pShutdownNotifier, randomSeed);
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
