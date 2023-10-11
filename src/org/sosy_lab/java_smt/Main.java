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

import java.math.BigDecimal;
import java.math.BigInteger;
import java.net.Inet4Address;
import java.util.ArrayList;
import java.util.List;
import org.sosy_lab.common.*;
import org.sosy_lab.common.configuration.*;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.*;
import org.sosy_lab.common.log.*;
import java.io.*;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;

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
    IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();
    BitvectorFormulaManager bimgr = fmgr.getBitvectorFormulaManager();

    BitvectorFormula a = bimgr.makeBitvector(6, 5);
    BitvectorFormula b = bimgr.makeBitvector(6, 30);
    BitvectorFormula x = bimgr.makeVariable(bimgr.getLength(b), "x");
    BitvectorFormula d = bimgr.makeBitvector(2, 2);
    BitvectorFormula f = bimgr.makeBitvector(3, 4);
    BitvectorFormula g = bimgr.extend(d, 1, true);

    BooleanFormula constraint = bimgr.equal(bimgr.and(a, bimgr.not(x)),
        bimgr.modulo(bimgr.shiftRight(a, bimgr.concat(g, f), true), b,false));

    //System.out.println(fmgr.dumpFormula(constraint));

    try (ProverEnvironment prover =
             context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS)) {
      prover.addConstraint(constraint);


      boolean isUnsat = prover.isUnsat();
      System.out.println("constraint is " + isUnsat + " and p = ");
      if (!isUnsat) {
        Model model = prover.getModel();
        BigInteger value = model.evaluate(x);
        System.out.println(value);

      }
    } catch (SolverException e) {
      throw new RuntimeException(e);
    }

  }
}

