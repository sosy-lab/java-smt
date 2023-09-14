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

import org.sosy_lab.common.*;
import org.sosy_lab.common.configuration.*;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.*;
import org.sosy_lab.common.log.*;
import java.io.*;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.utils.Generator;

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
            Solvers.PRINCESS);
    FormulaManager fmgr = context.getFormulaManager();
    BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();
    //IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();

    BooleanFormula p = bmgr.makeVariable("p");
    BooleanFormula q = bmgr.makeVariable("q");
    BooleanFormula t = bmgr.makeVariable("t");

    BooleanFormula constraint = bmgr.not(bmgr.and(q, bmgr.xor(bmgr.not(bmgr.or(p, bmgr.not(p)))
     , p)));
    BooleanFormula constraint1 = bmgr.equivalence(t, q);
    BooleanFormula constraint2 = bmgr.implication(t, bmgr.not(q));
    BooleanFormula constraint3 = bmgr.ifThenElse(p, q, t);

    try (ProverEnvironment prover =
             context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS)) {
      prover.addConstraint(constraint);
      prover.addConstraint(constraint1);
      prover.addConstraint(constraint2);
      prover.addConstraint(constraint3);
      boolean isUnsat = prover.isUnsat();
      if (!isUnsat) {
        Model model = prover.getModel();
        Boolean value = model.evaluate(p);
        //System.out.println("constraint is " + isUnsat + " and p = " + value);
      }
    } catch (SolverException e) {
      throw new RuntimeException(e);
    }

  }
}

