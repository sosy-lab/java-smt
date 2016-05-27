/*
 *
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
 *
 *
 */

package org.sosy_lab.solver.test;

import static com.google.common.truth.TruthJUnit.assume;

import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.SolverException;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.FormulaType.FloatingPointType;

import java.util.ArrayList;
import java.util.List;

@RunWith(Parameterized.class)
@SuppressFBWarnings(value = "DLS_DEAD_LOCAL_STORE")
public class VariableNamesTest extends SolverBasedTest0 {

  private final static String[] NAMES =
      new String[] {
        "as",
        "exists",
        "forall",
        "par",
        "let",
        "BINARY",
        "DECIMAL",
        "HEXADECIAML",
        "NUMERAL",
        "STRING",
        "define-fun",
        "declare",
        "get-model",
        "exit",
        " this is a quoted symbol ",
        " so is \n  this one ",
        " \" can occur too ",
        " af klj ^*0 asfe2 (&*)&(#^ $ > > >?\" ’]]984"
      };

  private final static String[] SPECIAL_NAMES =
      new String[] {
        "true",
        "false",
        "and",
        "or",
        "+",
        "-",
        "*",
        "=",
        "!=",
        "<",
        "<=",
        ">",
        ">=",
        "~",
        "!",
        ",",
        ".",
        ":",
        " ",
        "  ",
        "define-fun",
        "declare",
        "get-model",
        "exit",
        "(exit)",
        "|",
        "||",
        "|||",
        "|test",
        "|test|",
        "t|e|s|t",
        "(",
        ")",
        "[",
        "]",
        "{",
        "}",
        "[]",
        "\"",
        "''",
        "\"\"",
        "\\",
        "\n",
        "\t",
        "\u0000",
        "\u0001",
        "\u1234",
        "\u2e80",
        "| this is a quoted symbol |",
        " this is a quoted symbol ",
        "| so is \n  this one |",
        " so is \n  this one ",
        "| \" can occur too |",
        " \" can occur too ",
        "| af klj ^*0 asfe2 (&*)&(#^ $ > > >?\" ’]]984|",
        " af klj ^*0 asfe2 (&*)&(#^ $ > > >?\" ’]]984"
      };

  @Parameters(name = "{0} with varname {1}")
  public static List<Object[]> getAllCombinations() {
    List<Object[]> result = new ArrayList<>();
    for (Solvers solver : Solvers.values()) {
      for (String varname : NAMES) {
        result.add(new Object[] {solver, varname});
      }
      if (Solvers.SMTINTERPOL != solver) {
        for (String varname : SPECIAL_NAMES) {
          result.add(new Object[] {solver, varname});
        }
      }
    }
    return result;
  }

  @Parameter(0)
  public Solvers solver;

  @Parameter(1)
  public String varname;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Test
  public void testBoolVariable() {
    BooleanFormula var = bmgr.makeVariable(varname);
    @SuppressWarnings("unused")
    String dump = mgr.dumpFormula(var).toString();
  }

  @Test
  public void testBoolVariableEscaping() throws SolverException, InterruptedException {
    assume().that(solverToUse()).isNotEqualTo(Solvers.SMTINTERPOL);

    BooleanFormula var = bmgr.makeVariable(varname);
    @SuppressWarnings("unused")
    String dump = mgr.dumpFormula(var).toString();

    // depending on the solver, the toString-method might or might not escape the name.
    // TODO can we do anything to improve the solvers' behaviour? maybe not.
    if (varname.equals(var.toString())) {
      // not escaped -> we have the same variable
      BooleanFormula varFromString = bmgr.makeVariable(var.toString());
      assertThatFormula(var).isEquivalentTo(varFromString);

    } else {
      // escaped name -> creating it again should result in another (new) variable
      BooleanFormula varFromString = bmgr.makeVariable(var.toString());
      assertThatFormula(bmgr.xor(var, varFromString)).isSatisfiable();

      Assert.assertNotEquals(
          "name is escaped once, then the second call should escape it twice",
          varname,
          varFromString.toString());
      Assert.assertNotEquals(
          "name is escaped once, then the second call should escape it twice",
          mgr.dumpFormula(var).toString(),
          (mgr.dumpFormula(varFromString).toString()));
    }
  }

  @Test
  public void testIntVariable() {
    @SuppressWarnings("unused")
    Formula var = imgr.makeVariable(varname);
  }

  @Test
  public void testInvalidIntVariable() {
    @SuppressWarnings("unused")
    Formula var = imgr.makeVariable(varname);
  }

  @Test
  public void testInvalidRatVariable() {
    requireRationals();
    @SuppressWarnings("unused")
    Formula var = rmgr.makeVariable(varname);
  }

  @Test
  public void testBVVariable() {
    requireBitvectors();
    @SuppressWarnings("unused")
    Formula var = bvmgr.makeVariable(4, varname);
  }

  @Test
  public void testInvalidFloatVariable() {
    requireFloats();
    @SuppressWarnings("unused")
    Formula var =
        fpmgr.makeVariable(varname, FloatingPointType.getSinglePrecisionFloatingPointType());
  }

  @Test
  public void testArrayVariable() {
    requireArrays();
    @SuppressWarnings("unused")
    Formula var = amgr.makeArray(varname, FormulaType.IntegerType, FormulaType.IntegerType);
  }
}
