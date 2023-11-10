package org.sosy_lab.java_smt;/*
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

import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.*;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.*;
import java.io.*;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.utils.Generators.Generator;

public class Main {
  public static void main(String[] args)
      throws InvalidConfigurationException, InterruptedException, IOException, SolverException {
    String[] cmdLineArguments = new String[1];
    cmdLineArguments[0] = "--solver.generateSMTLIB2=true";
    Configuration config = Configuration.fromCmdLineArguments(cmdLineArguments);
    LogManager logger = BasicLogManager.create(config);
    ShutdownManager shutdown = ShutdownManager.create();
    SolverContext context =
        SolverContextFactory.createSolverContext(config, logger, shutdown.getNotifier(),
            Solvers.PRINCESS_BINARY);
    FormulaManager fmgr = context.getFormulaManager();
    BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();
    IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();
    BitvectorFormulaManager bvmgr = fmgr.getBitvectorFormulaManager();
    //RationalFormulaManager rmgr = fmgr.getRationalFormulaManager();
    UFManager umgr =  fmgr.getUFManager();

    //BooleanFormula constraint = fmgr.universalParse("/home/janel/Desktop/Studium/Semester_6"
     //   + "/Bachelorarbeit/nochmalneu/smtquery_mathsat/smtquery.022.smt2");

    BooleanFormula constraint = bmgr.makeVariable("a");

    try (ProverEnvironment prover =
             context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS,
                 ProverOptions.USE_BINARY)) {
      prover.addConstraint(constraint);

      Generator.dumpSMTLIB2();

      boolean isUnsat = prover.isUnsat();

      if (!isUnsat) {
        Model model = prover.getModel();
        System.out.println(model);
        Object value = model.evaluate(constraint);
        System.out.println(value);

      }


    } catch (SolverException v) {
      throw new RuntimeException(v);
    }
  }
}
