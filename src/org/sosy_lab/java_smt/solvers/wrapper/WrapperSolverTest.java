/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.wrapper;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.test.SolverBasedTest0;

@RunWith(Parameterized.class)
public class WrapperSolverTest extends SolverBasedTest0 {

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Test
  public void fooTest() {
    requireBitvectors();
    BitvectorType bv8 = FormulaType.getBitvectorTypeWithSize(8);
    BitvectorFormula x = bvmgr.makeVariable(bv8, "x");
    BitvectorFormula y = bvmgr.makeVariable(bv8, "y");

    CanonizingFormulaVisitor visitor = new CanonizingFormulaVisitor(mgr);
    mgr.visit(
        bmgr.ifThenElse(
            bvmgr.greaterThan(x, y, true),
            bvmgr.multiply(bvmgr.add(bvmgr.makeBitvector(8, 42), y), x),
            bvmgr.multiply(bvmgr.add(x, y), y)),
        visitor);

    CanonizingFormula formula = visitor.getStorage().getSomeConstraint();
    System.out.println("\n\n\t" + formula + "\n\n");
  }
}
