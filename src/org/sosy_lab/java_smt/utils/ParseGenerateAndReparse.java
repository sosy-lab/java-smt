// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0
package org.sosy_lab.java_smt.utils;

import com.microsoft.z3.*;
import com.microsoft.z3.Context;
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
    String smt2FileContent;
    try {
      smt2FileContent = Files.readString(Path.of(smt2FilePath), Charset.defaultCharset());
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
      try (SolverContext solverLessContext =
          SolverContextFactory.createSolverContext(
              config, logger, shutdown.getNotifier(), Solvers.SOLVERLESS)) {

        // JAVASMT'S PARSER
        BooleanFormula formula =
            solverLessContext.getFormulaManager().universalParseFromString(smt2FileContent);
        // JAVASMT'S GENERATOR
        Generator.assembleConstraint(formula);
        String regenerated = Generator.getSMTLIB2String();
        // NATIVE PARSE
        checkResult(checkNativeParseAndIsUnsat(solver, regenerated));
      } catch (Exception pE) {
        printError(pE);
      }
    }
    if (mode.equals("NATIVE")) {
      try {
        // NATIVE PARSE
        checkResult(checkNativeParseAndIsUnsat(solver, smt2FileContent));
      } catch (Exception pE) {
        printError(pE);
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
              realSolverContext.getFormulaManager().universalParseFromString(smt2FileContent);
          realProverEnvironment.addConstraint(javaSMTParsed);
          // JAVASMT'S PARSE
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

  public static boolean checkNativeParseAndIsUnsat(Solvers solver, String smt2)
      throws SolverException, InterruptedException, InvalidConfigurationException {
    switch (solver) {
      case Z3:
        return nativeZ3ParseAndIsUnsat(smt2);
      case MATHSAT5:
        return nativeMathSatParseAndIsUnsat(smt2);
      case BITWUZLA:
        return nativeBitwuzlaParseAndIsUnsat(smt2);
      default:
        throw new SolverException("Unsupported solver: " + solver);
    }
  }

  public static boolean nativeZ3ParseAndIsUnsat(String smt2) {
    try (Context ctx = new Context()) {
      Solver solver = ctx.mkSolver();
      solver.fromString(smt2);
      Status status = solver.check();
      return status == Status.UNSATISFIABLE;
    }
  }

  public static boolean nativeBitwuzlaParseAndIsUnsat(String smt2)
      throws InvalidConfigurationException, InterruptedException, SolverException {
    SolverContext bitwuz = SolverContextFactory.createSolverContext(Solvers.BITWUZLA);
    ProverEnvironment prover = bitwuz.newProverEnvironment(ProverOptions.GENERATE_MODELS);
    prover.addConstraint(bitwuz.getFormulaManager().parse(smt2));
    return prover.isUnsat();
  }

  public static boolean nativeMathSatParseAndIsUnsat(String smt2)
      throws InvalidConfigurationException, InterruptedException, SolverException {
    SolverContext mathsat = SolverContextFactory.createSolverContext(Solvers.MATHSAT5);
    ProverEnvironment prover = mathsat.newProverEnvironment(ProverOptions.GENERATE_MODELS);
    prover.addConstraint(mathsat.getFormulaManager().parse(smt2));
    return prover.isUnsat();
  }

  public static void printError(Exception pE) {
    if (pE instanceof UnsupportedOperationException) {
      System.out.println("UNSUPPORTED: ");
    } else {
      System.out.println("ERROR: ");
    }
    pE.printStackTrace();
    System.exit(1);
    throw new RuntimeException(pE);
  }
}
