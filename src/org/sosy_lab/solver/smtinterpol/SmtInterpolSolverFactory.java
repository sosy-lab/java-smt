/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.solver.smtinterpol;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.solver.SolverContextFactory;
import org.sosy_lab.solver.SolverContextFactory.InnerUtilFactory;
import org.sosy_lab.solver.api.SolverContext;

import javax.annotation.Nullable;

/**
 * Entry point for loading SmtInterpol.
 *
 * <p>Do not access this class directly, it needs to be loaded via
 * {@link SolverContextFactory}
 * because SmtInterpol needs to have it's own class loader.
 */
public class SmtInterpolSolverFactory implements InnerUtilFactory {

  // Needs to have default constructor because FormulaManagerFactory
  // calls it reflectively

  @Override
  public SolverContext create(
      Configuration pConfig,
      LogManager pLogger,
      ShutdownNotifier pShutdownNotifier,
      @Nullable PathCounterTemplate solverLogfile,
      long randomSeed)
      throws InvalidConfigurationException {
    final Thread currentThread = Thread.currentThread();
    final ClassLoader contextClassLoader = currentThread.getContextClassLoader();
    try {
      currentThread.setContextClassLoader(SmtInterpolSolverFactory.class.getClassLoader());
      return SmtInterpolSolverContext.create(
          pConfig, pLogger, pShutdownNotifier, solverLogfile, randomSeed);
    } finally {
      currentThread.setContextClassLoader(contextClassLoader);
    }
  }
}
