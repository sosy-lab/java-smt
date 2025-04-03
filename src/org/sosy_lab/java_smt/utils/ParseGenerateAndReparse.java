// Copyright (C) 2007-2016  Dirk Beyer
// SPDX-FileCopyrightText: 2025 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0
package org.sosy_lab.java_smt.utils;

import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.SExpr;
import edu.stanford.CVC4.SmtEngine;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
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
import com.microsoft.z3.*;
import io.github.cvc5.*;
import java.io.*;
import java.nio.file.*;
import io.github.cvc5.*;
import io.github.cvc5.modes.*;

/**
 * This file is meant for the Evaluation of the Parser/Generator.
 */
class ParseGenerateAndReparse {
  private ParseGenerateAndReparse() {
  }

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
      try (SolverContext solverLessContext =
               SolverContextFactory.createSolverContext(
                   config, logger, shutdown.getNotifier(), Solvers.SOLVERLESS)) {

        // JAVASMT'S PARSER
        BooleanFormula formula =
            solverLessContext.getFormulaManager().universalParseFromString(smt2);
        // JAVASMT'S GENERATOR
        Generator.assembleConstraint(formula);
        String regenerated = Generator.getSMTLIB2String();
        // NATIVE PARSE
        checkResult(callNativeParseAndIsUnsat(solver, smt2FilePath));
      } catch (Exception pE) {
        printError(pE);
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
          checkResult(callNativeParseAndIsUnsat(solver, smt2FilePath));
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
          //JAVASMT'S PARSE
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

  public static boolean nativeZ3ParseAndIsUnsat(String smt2) throws Exception {
    try (Context ctx = new Context()) {
      Solver solver = ctx.mkSolver();
      solver.fromString(smt2);
      Status status = solver.check();
      return status == Status.UNSATISFIABLE;
    }
  }

  public static boolean nativeCVC5ParseAndIsUnsat(String smt2) throws Exception {
    // 1. Temporäre Datei erstellen
    Path tempFile = Files.createTempFile("cvc5_", ".smt2");
    try {
      // 2. SMT2-Inhalt in temporäre Datei schreiben
      Files.write(tempFile, smt2.getBytes());

      // 3. Prozess für CVC5 starten
      ProcessBuilder pb = new ProcessBuilder(
          "./dependencies/cvc5",
          "--lang=smt2",
          tempFile.toString()
      );
      pb.redirectErrorStream(true);
      Process process = pb.start();

      // 4. Ausgabe lesen
      try (BufferedReader reader = new BufferedReader(
          new InputStreamReader(process.getInputStream()))) {
        String line;
        while ((line = reader.readLine()) != null) {
          if (line.trim().equals("unsat")) {
            return true;
          } else if (line.trim().equals("sat")) {
            return false;
          }
        }
      }

      // 5. Auf Prozessende warten
      int exitCode = process.waitFor();
      if (exitCode != 0) {
        throw new RuntimeException("CVC5 exited with code " + exitCode);
      }

      return false; // unknown
    } finally {
      // 6. Temporäre Datei löschen
      Files.deleteIfExists(tempFile);
    }
  }

  public static boolean nativeCVC4ParseAndIsUnsat(String smt2) throws Exception {
    // 1. Temporäre Datei erstellen
    Path tempFile = Files.createTempFile("cvc4_", ".smt2");
    try {
      // 2. SMT2-Inhalt in temporäre Datei schreiben
      Files.write(tempFile, smt2.getBytes());

      // 3. Prozess für CVC4 starten
      ProcessBuilder pb = new ProcessBuilder(
          "./dependencies/cvc4",
          "--lang=smt2",
          tempFile.toString()
      );
      pb.redirectErrorStream(true);
      Process process = pb.start();

      // 4. Ausgabe lesen
      try (BufferedReader reader = new BufferedReader(
          new InputStreamReader(process.getInputStream()))) {
        String line;
        while ((line = reader.readLine()) != null) {
          if (line.trim().equals("unsat")) {
            return true;
          } else if (line.trim().equals("sat")) {
            return false;
          }
        }
      }

      // 5. Auf Prozessende warten
      int exitCode = process.waitFor();
      if (exitCode != 0) {
        throw new RuntimeException("CVC4 exited with code " + exitCode);
      }

      return false; // unknown
    } finally {
      // 6. Temporäre Datei löschen
      Files.deleteIfExists(tempFile);
    }
  }

  public static boolean callNativeParseAndIsUnsat(Solvers solverName, String smt2)
      throws Exception {
    switch (solverName) {
      case Z3:
        return nativeZ3ParseAndIsUnsat(smt2);
      case CVC4:
        return nativeCVC4ParseAndIsUnsat(smt2);
      case CVC5:
        return nativeCVC5ParseAndIsUnsat(smt2);
      default:
        throw new UnsupportedOperationException("Unsupported solver: " + solverName);
    }
  }


  public static void printError(Exception pE) {
    System.out.println("ERROR: ");
    pE.printStackTrace();
    System.exit(1);
    throw new RuntimeException(pE);
  }
}
