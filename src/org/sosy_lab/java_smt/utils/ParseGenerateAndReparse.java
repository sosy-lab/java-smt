// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0
package org.sosy_lab.java_smt.utils;

import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Locale;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

/** This file is meant for the Evaluation of the Parser/Generator. */
class ParseGenerateAndReparse {
  private ParseGenerateAndReparse() {}

  public static void main(String[] args)
      throws InvalidConfigurationException, InterruptedException, SolverException {

    if (args.length < 2) {
      System.err.println("Usage: java ParseGenerateAndReparseTest <smt2-file> <solver>");
      System.exit(1);
    }

    // Lese den Inhalt der SMT2-Datei
    String smt2FilePath = args[0];
    String smt2;
    try {
      smt2 = Files.readString(Path.of(smt2FilePath), Charset.defaultCharset());
    } catch (IOException e) {
      System.err.println("Fehler beim Lesen der SMT2-Datei: " + smt2FilePath);
      e.printStackTrace();
      System.exit(1);
      return; // Unreachable, aber notwendig für Compiler
    }

    String solverName = args[1];

    // Try to get the solver
    Solvers solver;
    try {
      solver = Solvers.valueOf(solverName.toUpperCase(Locale.ROOT));
    } catch (IllegalArgumentException e) {
      System.err.println("Invalid solver name: " + solverName);
      System.exit(1);
      return; // Unreachable, aber notwendig für Compiler
    }

    // JavaSMT-Konfiguration
    Configuration config =
        Configuration.builder()
            .setOption("solver.generateSMTLIB2", "true")
            .setOption("solver.usedSolverBySolverLess", solverName)
            .build();
    LogManager logger = BasicLogManager.create(config);
    ShutdownManager shutdown = ShutdownManager.create();

    try (SolverContext z3solverContext =
             SolverContextFactory.createSolverContext(config, logger, shutdown.getNotifier(),
                 solver);
         SolverContext solverLessContext =
             SolverContextFactory.createSolverContext(config, logger, shutdown.getNotifier(),
                 Solvers.SOLVERLESS);
         ProverEnvironment z3proverEnv =
             z3solverContext.newProverEnvironment(ProverOptions.GENERATE_MODELS);
         ProverEnvironment solverLessProverEnv =
             solverLessContext.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
      try {
        z3proverEnv.addConstraint(
            z3solverContext.getFormulaManager().universalParseFromString(smt2));
      } catch (Exception pE) {
        if (pE instanceof UnsupportedOperationException) {
          System.out.println("RESULT UNKNOWN: Unsupported operation: " + pE.getMessage());
          System.exit(1);
        }
        System.out.println("Exception in first parsing: " + pE);
        System.exit(1);
      }
      try {
        solverLessProverEnv.addConstraint(
            solverLessContext.getFormulaManager().universalParseFromString(smt2));
      } catch (Exception pE) {
        if (pE instanceof UnsupportedOperationException) {
          System.out.println("RESULT UNKNOWN: Unsupported operation: " + pE.getMessage());
          System.exit(1);
        }
        System.out.println("Exception while Generating and Reparsing" + pE.getMessage());
        System.exit(1);
      }
      // Ergebnisse vergleichen
      boolean z3Sat = z3proverEnv.isUnsat();
      boolean reparsedSat = solverLessProverEnv.isUnsat();
      if (z3Sat == reparsedSat) {
        System.out.println("SUCCESS: " + z3Sat);
        System.exit(0);
      } else {
        System.out.println(
            "FAILURE: SolverSat:"
                + z3Sat
                + "is not equal to generated and "
                + "reparsed Sat: "
                + reparsedSat);
        System.exit(1);
      }
    }
  }
}
