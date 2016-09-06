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

import com.google.common.collect.ImmutableList;
import com.google.common.truth.Truth;

import org.junit.AssumptionViolatedException;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.visitors.ExpectedFormulaVisitor;

import java.util.List;

@RunWith(Parameterized.class)
public class UFManagerTest extends SolverBasedTest0 {
  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return Solvers.values();
  }

  @Parameter(0)
  public Solvers solver;

  @Override
  protected Solvers solverToUse() {
    return solver;
  }

  @Test
  public void testDeclareAndCallUF() {
    List<String> names = ImmutableList.of("Func", "|Func|", "(Func)");
    for (String name : names) {
      Formula f;
      try {
        f =
            fmgr.declareAndCallUF(
                name, FormulaType.IntegerType, ImmutableList.of(imgr.makeNumber(1)));
      } catch (RuntimeException e) {
        if (name.equals("|Func|")) {
          throw new AssumptionViolatedException("unsupported UF name", e);
        } else {
          throw e;
        }
      }
      FunctionDeclaration<?> declaration = getDeclaration(f);
      Truth.assertThat(declaration.getName()).isEqualTo(name);
      Formula f2 = mgr.makeApplication(declaration, imgr.makeNumber(1));
      Truth.assertThat(f2).isEqualTo(f);
    }
  }

  private FunctionDeclaration<?> getDeclaration(Formula f) {
    return mgr.visit(
        f,
        new ExpectedFormulaVisitor<FunctionDeclaration<?>>() {
          @Override
          public FunctionDeclaration<?> visitFunction(
              Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
            return functionDeclaration;
          }
        });
  }
}
