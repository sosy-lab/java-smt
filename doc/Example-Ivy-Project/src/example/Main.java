// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package example;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.SolverContext;

public class Main {
  public static void main(String[] args) {
    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = LogManager.createNullLogManager();
    ShutdownNotifier notifier = ShutdownNotifier.createDummy();

    for (Solvers solver : Solvers.values()) {
      try (SolverContext context =
          SolverContextFactory.createSolverContext(config, logger, notifier, solver)) {
        System.out.println(solver + ", " + context.getVersion());
      } catch (InvalidConfigurationException e) {
        System.out.println(solver + " not available");
      }
    }
  }
}
