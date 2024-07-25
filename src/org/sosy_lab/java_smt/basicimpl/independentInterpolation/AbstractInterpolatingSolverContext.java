/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl.independentInterpolation;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractSolverContext;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public abstract class AbstractInterpolatingSolverContext extends AbstractSolverContext {

  @Options(prefix = "solver")
  private static class SolverSettings {

    @Option(
        secure = true,
        description = "apply additional validation checks for interpolation results")
    protected boolean validateInterpolants = false;

    protected SolverSettings(Configuration config) throws InvalidConfigurationException {
      config.inject(this);
    }
  }

  // Creator is final, except after closing, then null.
  private FormulaCreator<?, ?, ?, ?> creator;
  private final ShutdownNotifier shutdownNotifier;
  private final int randomSeed;
  private final SolverSettings settings;
  private boolean closed = false;

  private AbstractInterpolatingSolverContext(
      FormulaCreator<?, ?, ?, ?> pCreator,
      FormulaManager pManager,
      ShutdownNotifier pShutdownNotifier,
      int pRandomSeed,
      SolverSettings pSettings) {
    super(pManager);
    creator = pCreator;
    shutdownNotifier = pShutdownNotifier;
    randomSeed = pRandomSeed;
    settings = pSettings;
  }

  protected abstract IndependentInterpolatingEnvironment<?> newProverEnvironmentWithIndependentInterpolation();

}
