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
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.utils.Generators.Generator;
import org.sosy_lab.java_smt.utils.Generators.UniversalModel;
import org.sosy_lab.java_smt.utils.Parsers.*;

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
            Solvers.CVC5);
    FormulaManager fmgr = context.getFormulaManager();
    BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();
    IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();
    //BitvectorFormulaManager bimgr = fmgr.getBitvectorFormulaManager();
    RationalFormulaManager rmgr = fmgr.getRationalFormulaManager();
    UFManager umgr =  fmgr.getUFManager();

    RationalFormula a = rmgr.makeNumber(-1);
    RationalFormula c = rmgr.makeNumber("3.4");
    RationalFormula e = rmgr.makeNumber(2147483.647);
    BooleanFormula constraint = rmgr.equal(a, rmgr.add(c, e));
    System.out.println(constraint);

    try (ProverEnvironment prover =
             context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS)) {
      prover.addConstraint(constraint);
      //prover.addConstraint(fmgr.universalParse("smtquery.002.smt2"));
      //prover.addConstraint(fmgr.parse("(declare-fun |id#2@1| () (_ BitVec 32))\n"
      //    + "(assert (and (bvsle |id#2@1| #x0000000a) (bvslt |id#2@1| #x00000000)))\n"
      //    + "(check-sat)"));

      //{id#2@1 -> mod_cast(0, 4294967295, 2147483648)}
      //{id#2@1 -> mod_cast(0, 4294967295, 2147483648)}

      boolean isUnsat = prover.isUnsat();
      if (!isUnsat) {
        Model model = prover.getModel();
        //Object value = model.evaluate(expectedFormula);
        System.out.println(model.getClass());

      }
      Generator.dumpSMTLIB2();
    } catch (SolverException v) {
      throw new RuntimeException(v);
    }
  }
}