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

import com.google.common.collect.ImmutableList;
import java.util.List;
import java.util.stream.Collectors;
import org.junit.Test;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

public class PortfolioSolverTest {

  @Test(expected = UnsupportedOperationException.class)
  public void testPortfolioUnsupportedCombination() throws InvalidConfigurationException {
    // TODO: more, also with less managers loaded
    loadAllPortfolioFormulaManagers(
        ImmutableList.of(Solvers.MATHSAT5, Solvers.Z3, Solvers.BITWUZLA));
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
