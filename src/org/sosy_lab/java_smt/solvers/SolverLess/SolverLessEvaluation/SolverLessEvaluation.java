/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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

package org.sosy_lab.java_smt.solvers.SolverLess.SolverLessEvaluation;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.Generator;

/**
 * This file is entirely for evaluation. The goal is to read an SMTLIB2 file - parse it into
 * JavaSMT functions and regenerate the SMTLIB2 file. Afterward we want to give both the output
 * and the input to a Solver (Z3) expecting that the 2 inputs are equivalent.
 */
public class SolverLessEvaluation {

  public static void main(String[] args)
      throws InvalidConfigurationException, IOException, SolverException, InterruptedException {
    String filePath = "input.smt2";
    System.out.println("SolverLessEvaluation - input file:");
    String fileContent = readFile(filePath);
    System.out.println(fileContent);
    System.out.println("--------\nParsed and regenerated query: ");
    Configuration config = Configuration.fromCmdLineArguments(args);
    LogManager logger = BasicLogManager.create(config);
    ShutdownManager shutdown = ShutdownManager.create();
    SolverContext context = SolverContextFactory.createSolverContext(
        config, logger, shutdown.getNotifier(), Solvers.SOLVERLESS);

    FormulaManager fmgr = context.getFormulaManager();
    BooleanFormula parsedResult = fmgr.universalParseFromString(fileContent);
    Generator.assembleConstraint(parsedResult);
    String regenerated = String.valueOf(Generator.getLines());
    System.out.println(regenerated);

  }
  public static String readFile(String fileName) {
    String sourceName = "src/org/sosy_lab/java_smt/solvers/SolverLess/SolverLessEvaluation"+"/" + fileName;

    StringBuilder inputFromFile = new StringBuilder();
    try {
      BufferedReader reader = new BufferedReader(new FileReader(sourceName));
      String line;

      while ((line = reader.readLine()) != null) {
        inputFromFile.append(line).append("\n");
      }

      reader.close();

    } catch (IOException e) {
      System.out.println("Error: " + e.getMessage());
    }

    return inputFromFile.toString();
  }



}
