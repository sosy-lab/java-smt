/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;

import com.google.common.collect.ImmutableList;
import java.util.List;
import java.util.stream.Collectors;
import org.junit.After;
import org.junit.Test;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class PortfolioSolverTest {

  private SolverContext context = null;
  private ProverEnvironment prover = null;
  private FormulaManager pfmgr;

  @After
  public void after() {
    close();
  }

  /** Test bool solving with all solvers supporting it and check that a model is retrievable. */
  @SuppressWarnings("CheckReturnValue")
  @Test
  public void testPortfolioBasicBoolSolving()
      throws InvalidConfigurationException, InterruptedException, SolverException {
    // TODO: more, also with less/more managers etc
    // CVC5, Boolector, CVC4 can not translate formulas currently
    List<Solvers> solvers =
        ImmutableList.of(
            Solvers.MATHSAT5, Solvers.Z3, Solvers.CVC5, Solvers.SMTINTERPOL, Solvers.BITWUZLA);
    loadPortfolioSolverWithProver(solvers);

    BooleanFormulaManager pbmgr = pfmgr.getBooleanFormulaManager();
    BooleanFormula f = pbmgr.makeFalse();
    BooleanFormula a = pbmgr.makeVariable("a");
    BooleanFormula b = pbmgr.makeVariable("b");

    BooleanFormula aOrFalse = pbmgr.or(a, f);
    BooleanFormula aEqTrue = pbmgr.and(a, f);
    BooleanFormula right = pbmgr.and(f, b);
    BooleanFormula impl = pbmgr.implication(a, right);

    for (Solvers solver : solvers) {
      assertThat(impl.toString()).contains(solver.name());
    }

    // (a -> (false AND b)) AND (a or false) SAT with a = false
    prover.addConstraint(impl);
    prover.addConstraint(aOrFalse);
    assertThat(prover.isUnsat()).isFalse();
    // Get model, but ignore
    prover.getModel();
    // prover.getModelAssignments();
    // prover.getEvaluator();

    // (a AND false) AND (a -> (false AND b)) AND (a or false) UNSAT
    prover.addConstraint(aEqTrue);
    assertThat(prover.isUnsat()).isTrue();
  }

  // The portfolio can't translate due to missing parse/dump support in all solvers
  @Test(expected = UnsupportedOperationException.class)
  public void testPortfolioProverTranslationFailure()
      throws InvalidConfigurationException, InterruptedException, SolverException {
    // TODO: more, also with less/more managers etc
    List<Solvers> solvers = ImmutableList.of(Solvers.CVC4, Solvers.CVC5);
    loadPortfolioSolverWithProver(solvers);

    BooleanFormulaManager pbmgr = pfmgr.getBooleanFormulaManager();
    BooleanFormula f = pbmgr.makeFalse();
    BooleanFormula a = pbmgr.makeVariable("a");
    BooleanFormula b = pbmgr.makeVariable("b");

    BooleanFormula right = pbmgr.and(f, b);
    BooleanFormula impl = pbmgr.implication(a, right);

    for (Solvers solver : solvers) {
      assertThat(impl.toString()).contains(solver.name());
    }

    // a -> (false AND b)  SAT with a = false
    prover.addConstraint(impl);
    assertThat(prover.isUnsat()).isFalse();
  }

  @Test(expected = UnsupportedOperationException.class)
  public void testPortfolioUnsupportedCombination() throws InvalidConfigurationException {
    // TODO: more, also with less managers loaded
    loadAllPortfolioFormulaManagers(
        ImmutableList.of(Solvers.MATHSAT5, Solvers.Z3, Solvers.BITWUZLA));
  }

  private void loadPortfolioSolverWithProver(List<Solvers> pSolversList)
      throws InvalidConfigurationException {
    Configuration config = createPortfolioTestConfig(pSolversList);
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();
    context = SolverContextFactory.createSolverContext(config, logger, notifier, Solvers.PORTFOLIO);
    pfmgr = context.getFormulaManager();

    prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS);
  }

  private void close() {
    if (prover != null) {
      prover.close();
    }
    if (context != null) {
      context.close();
    }
  }

  @SuppressWarnings({"CheckReturnValue", "UnusedVariable"})
  private void loadAllPortfolioFormulaManagers(List<Solvers> pSolversList)
      throws InvalidConfigurationException {
    Configuration config = createPortfolioTestConfig(pSolversList);
    LogManager logger = BasicLogManager.create(config);
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();
    try (SolverContext context =
        SolverContextFactory.createSolverContext(config, logger, notifier, Solvers.PORTFOLIO)) {
      ProverEnvironment proverBeforeFormula =
          context.newProverEnvironment(ProverOptions.GENERATE_MODELS);
      FormulaManager fmgr = context.getFormulaManager();
      fmgr.getBooleanFormulaManager();
      fmgr.getIntegerFormulaManager();
      fmgr.getBitvectorFormulaManager();
      fmgr.getArrayFormulaManager();
      fmgr.getQuantifiedFormulaManager();
      fmgr.getUFManager();
      fmgr.getFloatingPointFormulaManager();
      fmgr.getSLFormulaManager();
      fmgr.getStringFormulaManager();
      fmgr.getEnumerationFormulaManager();
    }
  }

  private Configuration createPortfolioTestConfig(List<Solvers> pSolversList)
      throws InvalidConfigurationException {
    return Configuration.builder()
        .setOption("solver.solver", Solvers.PORTFOLIO.name())
        .setOption(
            "solver.portfolio.solvers",
            pSolversList.stream().map(Enum::name).collect(Collectors.joining(",")))
        .build();
  }
}
