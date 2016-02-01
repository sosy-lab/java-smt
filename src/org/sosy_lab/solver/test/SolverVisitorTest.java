/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.solver.SolverContextFactory.Solvers;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.solver.api.ProverEnvironment;
import org.sosy_lab.solver.visitors.BooleanFormulaTransformationVisitor;
import org.sosy_lab.solver.visitors.BooleanFormulaVisitor;
import org.sosy_lab.solver.visitors.DefaultFormulaVisitor;
import org.sosy_lab.solver.visitors.FormulaVisitor;
import org.sosy_lab.solver.visitors.TraversalProcess;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

@RunWith(Parameterized.class)
public class SolverVisitorTest extends SolverBasedTest0 {

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

  private ProverEnvironment env;

  @Before
  public void setupEnvironment() {
    env = context.newProverEnvironment();
  }

  @After
  public void closeEnvironment() {
    env.close();
  }

  @Test
  public void booleanIdVisit() {
    BooleanFormula t = bmgr.makeBoolean(true);
    BooleanFormula f = bmgr.makeBoolean(false);
    BooleanFormula x = bmgr.makeVariable("x");
    BooleanFormula y = bmgr.makeVariable("y");
    BooleanFormula z = bmgr.makeVariable("z");
    BooleanFormula and = bmgr.and(x, y);
    BooleanFormula or = bmgr.or(x, y);
    BooleanFormula ite = bmgr.ifThenElse(x, and, or);
    BooleanFormula impl = bmgr.implication(z, y);
    BooleanFormula eq = bmgr.equivalence(t, y);
    BooleanFormula not = bmgr.not(eq);

    for (BooleanFormula bf : Lists.newArrayList(t, f, x, y, z, and, or, ite, impl, eq, not)) {
      BooleanFormulaVisitor<BooleanFormula> identityVisitor =
          new BooleanFormulaTransformationVisitor(
              mgr, new HashMap<BooleanFormula, BooleanFormula>()) {
            // we need a subclass, because the original class is 'abstract'
          };
      assertThatFormula(bmgr.visit(identityVisitor, bf)).isEqualTo(bf);
    }
  }

  @Test
  public void booleanIdVisitWithAtoms() {
    IntegerFormula n12 = imgr.makeNumber(12);
    IntegerFormula a = imgr.makeVariable("a");
    IntegerFormula b = imgr.makeVariable("b");
    IntegerFormula sum = imgr.add(a, b);
    IntegerFormula diff = imgr.subtract(a, b);
    IntegerFormula neg = imgr.negate(a);
    BooleanFormula eq = imgr.equal(n12, a);
    IntegerFormula ite = bmgr.ifThenElse(eq, sum, diff);

    for (IntegerFormula f : Lists.newArrayList(a, b, n12, neg, ite)) {
      BooleanFormulaVisitor<BooleanFormula> identityVisitor =
          new BooleanFormulaTransformationVisitor(
              mgr, new HashMap<BooleanFormula, BooleanFormula>()) {
            // we need a subclass, because the original class is 'abstract'
          };
      BooleanFormula bf = imgr.equal(n12, f);
      assertThatFormula(bmgr.visit(identityVisitor, bf)).isEqualTo(bf);
    }
  }

  /**
   * A very basic test for the formula visitor, defines a visitor
   * which gathers all found free variables.
   */
  @Test
  public void testFormulaVisitor() {
    IntegerFormula x, y, z;
    x = imgr.makeVariable("x");
    y = imgr.makeVariable("y");
    z = imgr.makeVariable("z");

    BooleanFormula f = bmgr.or(imgr.equal(z, imgr.add(x, y)), imgr.equal(x, imgr.add(z, y)));

    final Set<String> usedVariables = new HashSet<>();

    FormulaVisitor<TraversalProcess> nameExtractor =
        new DefaultFormulaVisitor<TraversalProcess>() {
          @Override
          protected TraversalProcess visitDefault(Formula f) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitFreeVariable(Formula f, String name) {
            usedVariables.add(name);
            return TraversalProcess.CONTINUE;
          }
        };
    mgr.visitRecursively(nameExtractor, f);
    assertThat(usedVariables).isEqualTo(Sets.newHashSet("x", "y", "z"));
  }

  @Test
  public void testBooleanFormulaQuantifierHandling() throws Exception {
    requireQuantifiers();

    // TODO: currently neither Z3 nor Princess is working with quantifiers
    // properly due to bugs on our side =(.
    assume().that(solverToUse()).isNoneOf(Solvers.PRINCESS, Solvers.Z3, Solvers.Z3JAVA);

    assert qmgr != null;

    BooleanFormula x = bmgr.makeVariable("x");
    BooleanFormula constraint = qmgr.forall(ImmutableList.of(x), x);
    assertThatFormula(constraint).isUnsatisfiable();
    BooleanFormula newConstraint =
        bmgr.visit(
            new BooleanFormulaTransformationVisitor(
                mgr, new HashMap<BooleanFormula, BooleanFormula>()) {},
            constraint);
    assertThatFormula(newConstraint).isUnsatisfiable();
  }

  @Test
  public void testVisitingTrue() throws Exception {

    // Check that "true" is correctly treated as a constant.
    BooleanFormula t = bmgr.makeBoolean(true);
    final List<Boolean> containsTrue = new ArrayList<>();
    mgr.visitRecursively(
        new DefaultFormulaVisitor<TraversalProcess>() {
          @Override
          protected TraversalProcess visitDefault(Formula f) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitConstant(Formula f, Object o) {
            if (f.equals(bmgr.makeBoolean(true))) {
              containsTrue.add(true);
            }
            return TraversalProcess.CONTINUE;
          }
        },
        t);
    assertThat(containsTrue).isNotEmpty();
  }
}
