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
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.Generator;

/** This file is meant for the Evaluation of the Parser/Generator. */
class ParseGenerateAndReparse {
  private ParseGenerateAndReparse() {}

  public static void main(String[] args)
      throws InvalidConfigurationException, InterruptedException, SolverException {

    if (args.length < 3) {
      System.err.println("Usage: java ParseGenerateAndReparseTest <smt2-file> <solver> <mode>");
      System.exit(1);
    }

    String smt2FilePath = args[0];
    String smt2;
    try {
      smt2 = Files.readString(Path.of(smt2FilePath), Charset.defaultCharset());
    } catch (IOException e) {
      System.err.println("Fehler beim Lesen der SMT2-Datei: " + smt2FilePath);
      e.printStackTrace();
      System.exit(1);
      return;
    }

    String solverName = args[1];
    Solvers solver;
    try {
      solver = Solvers.valueOf(solverName.toUpperCase(Locale.ROOT));
    } catch (IllegalArgumentException e) {
      System.err.println("Invalid solver name: " + solverName);
      System.exit(1);
      return;
    }
    String mode = args[2].toUpperCase(Locale.ROOT);
    Configuration config =
        Configuration.builder()
            .setOption("solver.generateSMTLIB2", "true")
            .setOption("solver.usedSolverBySolverLess", solverName)
            .build();
    LogManager logger = BasicLogManager.create(config);
    ShutdownManager shutdown = ShutdownManager.create();

    if (mode.equals("GENERATE_AND_REPARSE")) {
      // PARSE REGENERATE THEN NATIVE PARSE
      try (SolverContext realSolverContext =
              SolverContextFactory.createSolverContext(
                  config, logger, shutdown.getNotifier(), solver);
          SolverContext solverLessContext =
              SolverContextFactory.createSolverContext(
                  config, logger, shutdown.getNotifier(), Solvers.SOLVERLESS);
          ProverEnvironment realProverEnvironment =
              realSolverContext.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {

        try {
          // JAVASMT'S PARSER
          BooleanFormula formula =
              solverLessContext.getFormulaManager().universalParseFromString(smt2);
          // JAVASMT'S GENERATOR
          Generator.assembleConstraint(formula);
          String regenerated = Generator.getSMTLIB2String();
          // NATIVE PARSE
          BooleanFormula reparsed = realSolverContext.getFormulaManager().parse(regenerated);
          realProverEnvironment.addConstraint(reparsed);
          checkResult(realProverEnvironment.isUnsat());

        } catch (Exception pE) {
          printError(pE);
        }
      }
    }
    if (mode.equals("NATIVE")) {
      try (SolverContext realSolverContext =
              SolverContextFactory.createSolverContext(
                  config, logger, shutdown.getNotifier(), solver);
          ProverEnvironment realProverEnvironment =
              realSolverContext.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {

        try {
          // NATIVE PARSE
          BooleanFormula nativeParsed = realSolverContext.getFormulaManager().parse(smt2);
          realProverEnvironment.addConstraint(nativeParsed);
          checkResult(realProverEnvironment.isUnsat());
        } catch (Exception pE) {
          printError(pE);
        }
      }
    }
    if (mode.equals("PARSE")) {
      try (SolverContext realSolverContext =
              SolverContextFactory.createSolverContext(
                  config, logger, shutdown.getNotifier(), solver);
          ProverEnvironment realProverEnvironment =
              realSolverContext.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
        try {
          // JAVASMT'S PARSER
          BooleanFormula javaSMTParsed =
              realSolverContext.getFormulaManager().universalParseFromString(smt2);
          realProverEnvironment.addConstraint(javaSMTParsed);
          checkResult(realProverEnvironment.isUnsat());
        } catch (Exception pE) {
          printError(pE);
        }
      }
    }
  }

  public static void checkResult(boolean isUnsat) {
    System.out.println("SUCCESS: isUnsat = " + isUnsat);
    System.exit(0);
  }

  public static void printError(Exception pE) {
    System.out.println("ERROR: ");
    pE.printStackTrace();
    System.exit(1);
    throw new RuntimeException(pE);
  }
}
