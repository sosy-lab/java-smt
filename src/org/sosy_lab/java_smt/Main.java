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

import java.nio.file.Files;
import java.nio.file.Path;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.*;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.*;
import java.io.*;
import org.sosy_lab.java_smt.utils.Parsers.*;

public class Main {
  public static void main(String[] args)
      throws InvalidConfigurationException, InterruptedException, IOException, SolverException {
    String fileName = "smtquery.053.smt2";

    String smtlib2 = Files.readString(Path.of(fileName));


    smtlibv2Lexer lexer = new smtlibv2Lexer(CharStreams.fromFileName(fileName));
    smtlibv2Parser parser = new smtlibv2Parser(new CommonTokenStream(lexer));

    Configuration config = Configuration.defaultConfiguration();
    LogManager logger = BasicLogManager.create(config);
    ShutdownManager shutdown = ShutdownManager.create();
    SolverContext context =
        SolverContextFactory.createSolverContext(config, logger, shutdown.getNotifier(),
            Solvers.PRINCESS);

    FormulaManager fmgr = context.getFormulaManager();

    BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();
    IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();
    //RationalFormulaManager rmgr = fmgr.getRationalFormulaManager();
    BitvectorFormulaManager bimgr = fmgr.getBitvectorFormulaManager();
    ArrayFormulaManager amgr = fmgr.getArrayFormulaManager();
    UFManager umgr = fmgr.getUFManager();

    BooleanFormula test = fmgr.parse( "(declare-fun |id#1@1| () (_ BitVec 32))\n"
        + "(assert (bvslt (_ bv10 32) |id#1@1|))\n"
        + "(check-sat)\n"
        + "(exit)\n"
    );
// {id#1@1 -> mod_cast(0, 4294967295, 2147483647)}
    BooleanFormula constraint = fmgr.universalParse(fileName);

    try (ProverEnvironment prover =
             context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS)) {
      prover.addConstraint(constraint);

      boolean isUnsat = prover.isUnsat();
      if (isUnsat) {
        System.out.println("unsat");
      }
      if (!isUnsat) {
        System.out.println("sat");
        Model model = prover.getModel();
        //Object value = model.evaluate(y);
        System.out.println(model);

      }
    } catch (SolverException e) {
      throw new RuntimeException(e);
    }

  }
}

