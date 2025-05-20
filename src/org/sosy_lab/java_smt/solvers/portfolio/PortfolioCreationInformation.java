/*
 * This file is part of JavaSMT;
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.portfolio;

import java.util.function.Consumer;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;

public class PortfolioCreationInformation {

  private final Configuration config;
  private final LogManager logger;
  private final ShutdownNotifier shutdownNotifier;
  private final @Nullable PathCounterTemplate solverLogfile;
  private final long randomSeed;
  private final FloatingPointRoundingMode floatingPointRoundingMode;
  private final NonLinearArithmetic nonLinearArithmetic;
  private final Consumer<String> loader;

  protected PortfolioCreationInformation(
      Configuration pConfig,
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate pSolverLogfile,
      long pRandomSeed,
      FloatingPointRoundingMode pFloatingPointRoundingMode,
      NonLinearArithmetic pNonLinearArithmetic,
      Consumer<String> pLoader) {
    config = pConfig;
    logger = pLogger;
    shutdownNotifier = pShutdownNotifier;
    solverLogfile = pSolverLogfile;
    randomSeed = pRandomSeed;
    floatingPointRoundingMode = pFloatingPointRoundingMode;
    nonLinearArithmetic = pNonLinearArithmetic;
    loader = pLoader;
  }

  protected Configuration getConfig() {
    return config;
  }

  protected LogManager getLogger() {
    return logger;
  }

  protected ShutdownNotifier getShutdownNotifier() {
    return shutdownNotifier;
  }

  protected @Nullable PathCounterTemplate getSolverLogfile() {
    return solverLogfile;
  }

  protected long getRandomSeed() {
    return randomSeed;
  }

  protected FloatingPointRoundingMode getFloatingPointRoundingMode() {
    return floatingPointRoundingMode;
  }

  protected NonLinearArithmetic getNonLinearArithmetic() {
    return nonLinearArithmetic;
  }

  protected Consumer<String> getLoader() {
    return loader;
  }
}
