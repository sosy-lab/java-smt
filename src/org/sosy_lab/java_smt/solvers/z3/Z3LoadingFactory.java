// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.InnerUtilFactory;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager.NonLinearArithmetic;

/**
 * Entry point for loading Z3.
 *
 * <p>Do not access this class directly, it needs to be loaded via {@link SolverContextFactory}
 * because Z3 needs to have its own class loader.
 */
public class Z3LoadingFactory extends InnerUtilFactory {
  @Override
  public SolverContext generateSolverContext(
      Configuration config,
      LogManager logger,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate solverLogfile,
      long randomSeed,
      FloatingPointRoundingMode pFloatingPointRoundingMode,
      NonLinearArithmetic pNonLinearArithmetic)
      throws InvalidConfigurationException {

    return Z3SolverContext.create(
        logger,
        config,
        pShutdownNotifier,
        solverLogfile,
        randomSeed,
        pFloatingPointRoundingMode,
        pNonLinearArithmetic);
  }
}
