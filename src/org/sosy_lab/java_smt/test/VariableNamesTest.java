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

import static com.google.common.collect.FluentIterable.from;
import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.Truth.assert_;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.errorprone.annotations.CanIgnoreReturnValue;
import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;
import java.util.Arrays;
import java.util.List;
import java.util.function.Function;
import org.junit.AssumptionViolatedException;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.visitors.DefaultBooleanFormulaVisitor;

@RunWith(Parameterized.class)
@SuppressFBWarnings(value = "DLS_DEAD_LOCAL_STORE")
public class VariableNamesTest extends SolverBasedTest0 {

  private static final ImmutableList<String> NAMES =
      ImmutableList.of(
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
          "(exit)",
          "!=",
          "~",
          ",",
          ".",
          ":",
          " ",
          "  ",
          "(",
          ")",
          "[",
          "]",
          "{",
          "}",
          "[]",
          "\"",
          "''",
          "\n",
          "\t",
          "\u0000",
          "\u0001",
          "\u1234",
          "\u2e80",
          " this is a quoted symbol ",
          " so is \n  this one ",
          " \" can occur too ",
          " af klj ^*0 asfe2 (&*)&(#^ $ > > >?\" ’]]984");

  private static final ImmutableSet<String> POSSIBLY_UNSUPPORTED_NAMES =
      ImmutableSet.of(
          "true",
          "false",
          "and",
          "or",
          "select",
          "store",
          "|",
          "||",
          "|||",
          "|test",
          "|test|",
          "t|e|s|t",
          "\"\"",
          "\\",
          "| this is a quoted symbol |",
          "| so is \n  this one |",
          "| \" can occur too |",
          "| af klj ^*0 asfe2 (&*)&(#^ $ > > >?\" ’]]984|");

  @SuppressWarnings("unchecked")
  @Parameters(name = "{0} with varname {1}")
  public static List<Object[]> getAllCombinations() {
    List<String> allNames = from(NAMES).append(POSSIBLY_UNSUPPORTED_NAMES).toList();
    return Lists.transform(
        Lists.cartesianProduct(Arrays.asList(Solvers.values()), allNames), List::toArray);
  }

  @Parameter(0)
  public Solvers solver;

  @Parameter(1)
  public String varname;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @CanIgnoreReturnValue
  private <T extends Formula> T createVariableWith(Function<String, T> creator) {
    try {
      return creator.apply(varname);
    } catch (RuntimeException e) {
      if (POSSIBLY_UNSUPPORTED_NAMES.contains(varname)) {
        // Solvers may or may not support variables with this name
        throw new AssumptionViolatedException("unsupported variable name", e);
      } else {
        throw e;
      }
    }
  }

  @Test
  public void testBoolVariable() {
    createVariableWith(bmgr::makeVariable);
  }

  @Test
  public void testBoolVariableEscaping() throws SolverException, InterruptedException {
    BooleanFormula var = createVariableWith(bmgr::makeVariable);

    if (varname.equals(var.toString())) {
      // Check that variable is indeed the same if we re-create it
      BooleanFormula varFromString = bmgr.makeVariable(var.toString());
      assertThatFormula(var).isEquivalentTo(varFromString);

    } else {
      // escaped name
      assertThat(var.toString()).startsWith("|");
      assertThat(var.toString()).endsWith("|");

      // creating it again should result in another (new) variable,
      // but creating it again does not work with SMTInterpol
      assume().that(solver).isNotEqualTo(Solvers.SMTINTERPOL);
      BooleanFormula varFromString = bmgr.makeVariable(var.toString());
      assertThatFormula(bmgr.xor(var, varFromString)).isSatisfiable();

      assert_()
          .withMessage("name is escaped once, then the second call should escape it twice")
          .that(varFromString.toString())
          .isNotEqualTo(varname);
      assert_()
          .withMessage("name is escaped once, then the second call should escape it twice")
          .that(mgr.dumpFormula(varFromString).toString())
          .isNotEqualTo(mgr.dumpFormula(var).toString());
    }
  }

  @Test
  public void testBoolVariableNameInVisitor() {
    BooleanFormula var = createVariableWith(bmgr::makeVariable);

    bmgr.visit(
        var,
        new DefaultBooleanFormulaVisitor<Void>() {
          @Override
          protected Void visitDefault() {
            throw new AssertionError("unexpected case");
          }

          @Override
          public Void visitAtom(BooleanFormula pAtom, FunctionDeclaration<BooleanFormula> pDecl) {
            assertThat(pDecl.getName()).isEqualTo(varname);
            return null;
          }
        });
  }

  @Test
  public void testBoolVariableDump() {
    BooleanFormula var = createVariableWith(bmgr::makeVariable);
    @SuppressWarnings("unused")
    String dump = mgr.dumpFormula(var).toString();
  }

  @Test
  public void testIntVariable() {
    createVariableWith(imgr::makeVariable);
  }

  @Test
  public void testInvalidRatVariable() {
    requireRationals();
    createVariableWith(rmgr::makeVariable);
  }

  @Test
  public void testBVVariable() {
    requireBitvectors();
    createVariableWith(v -> bvmgr.makeVariable(4, v));
  }

  @Test
  public void testInvalidFloatVariable() {
    requireFloats();
    createVariableWith(
        v -> fpmgr.makeVariable(v, FormulaType.getSinglePrecisionFloatingPointType()));
  }

  @Test
  public void testArrayVariable() {
    requireArrays();
    createVariableWith(v -> amgr.makeArray(v, FormulaType.IntegerType, FormulaType.IntegerType));
  }
}
