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
import java.util.ArrayList;
import java.util.List;
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
    String fileName = "smtquery.017.smt2";

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

    BooleanFormula test = fmgr.parse( "(set-logic AUFLIRA)\n"
        + "(declare-fun |id#2@1| () (_ BitVec 32))\n"
        + "(declare-fun |id#0@1| () (_ BitVec 32))\n"
        + "(define-fun .10 () (_ BitVec 32) (_ bv10 32))\n"
        + "(define-fun .20 () (_ BitVec 32) |id#2@1|)\n"
        + "(define-fun .22 () Bool (bvslt .10 .20))\n"
        + "(define-fun .23 () Bool (not .22))\n"
        + "(define-fun .29 () (_ BitVec 1) (_ bv1 1))\n"
        + "(define-fun .30 () (_ BitVec 1) ((_ extract 31 31) .20))\n"
        + "(define-fun .31 () Bool (= .30 .29))\n"
        + "(define-fun .52 () Bool (not .31))\n"
        + "(define-fun .55 () (_ BitVec 32) |id#0@1|)\n"
        + "(define-fun .56 () Bool (bvslt .10 .55))\n"
        + "(define-fun .62 () Bool (not .56))\n"
        + "(define-fun .68 () (_ BitVec 1) ((_ extract 31 31) .55))\n"
        + "(define-fun .69 () Bool (= .68 .29))\n"
        + "(define-fun .89 () Bool (not .69))\n"
        + "(define-fun .92 () Bool (= .20 .55))\n"
        + "(define-fun .94 () Bool (and .52 .89))\n"
        + "(define-fun .101 () Bool (not .92))\n"
        + "(define-fun .103 () Bool (and .62 .94))\n"
        + "(define-fun .104 () Bool (and .101 .103))\n"
        + "(define-fun .105 () Bool (and .23 .104))\n"
        + "(assert .105)\n"

    );


    BooleanFormula constraint = fmgr.universalParse(fileName);

    try (ProverEnvironment prover =
             context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS)) {
      prover.addConstraint(constraint);

      //{id#0@1 -> mod_cast(0, 4294967295, 10), id#2@1 -> mod_cast(0, 4294967295, 9)}

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

