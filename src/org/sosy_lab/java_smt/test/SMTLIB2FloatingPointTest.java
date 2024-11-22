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

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;

import java.io.IOException;
import org.junit.Test;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.SolverException;

public class SMTLIB2FloatingPointTest extends SolverBasedTest0{
  @Override
  protected Solvers solverToUse() {
    return Solvers.Z3;
  }
  @Test
  public void testDeclareFloatingPoints()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-fun a () (_ FloatingPoint 8 24))\n"
            + "(declare-fun b () (_ FloatingPoint 8 24))\n"
            + "(assert (= a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a =
        fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula b =
        fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 24));

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

  @Test
  public void testFloatingPointAddition()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-fun a () (_ FloatingPoint 8 24))\n"
            + "(declare-fun b () (_ FloatingPoint 8 24))\n"
            + "(declare-fun c () (_ FloatingPoint 8 24))\n"
            + "(assert (= c (fp.add RNE a b)))\n";


    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a =
        fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula b =
        fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula c =
        fpmgr.makeVariable("c", FormulaType.getFloatingPointType(8, 24));

    FloatingPointFormula additionResult =
        fpmgr.add(a, b, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN);

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(c, additionResult);

    BooleanFormula expectedResult = constraint;

    assertThat(actualResult).isEqualTo(expectedResult);
  }

}
