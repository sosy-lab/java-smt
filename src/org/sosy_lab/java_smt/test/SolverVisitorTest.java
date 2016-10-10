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
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Sets;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.stream.Collectors;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.DefaultBooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

@RunWith(Parameterized.class)
public class SolverVisitorTest extends SolverBasedTest0 {

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

    for (BooleanFormula bf : ImmutableList.of(t, f, x, y, z, and, or, ite, impl, eq, not)) {
      BooleanFormulaVisitor<BooleanFormula> identityVisitor =
          new BooleanFormulaTransformationVisitor(mgr) {
            // we need a subclass, because the original class is 'abstract'
          };
      assertThatFormula(bmgr.visit(bf, identityVisitor)).isEqualTo(bf);
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

    for (IntegerFormula f : ImmutableList.of(a, b, n12, neg, ite)) {
      BooleanFormulaVisitor<BooleanFormula> identityVisitor =
          new BooleanFormulaTransformationVisitor(mgr) {};
      BooleanFormula bf = imgr.equal(n12, f);
      assertThatFormula(bmgr.visit(bf, identityVisitor)).isEqualTo(bf);
    }
  }

  /**
   * A very basic test for the formula visitor, defines a visitor which gathers all found free
   * variables.
   */
  @Test
  public void testFormulaVisitor() {
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula z = imgr.makeVariable("z");

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
    mgr.visitRecursively(f, nameExtractor);
    assertThat(usedVariables).isEqualTo(Sets.newHashSet("x", "y", "z"));
  }

  @Test
  public void testBooleanFormulaQuantifierHandling() throws Exception {
    requireQuantifiers();
    // TODO Maybe rewrite using quantified integer variable to allow testing with Princess
    assume()
        .withFailureMessage("Princess does not support quantifier over boolean variables")
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);

    BooleanFormula x = bmgr.makeVariable("x");
    BooleanFormula constraint = qmgr.forall(ImmutableList.of(x), x);
    assertThatFormula(constraint).isUnsatisfiable();
    BooleanFormula newConstraint =
        bmgr.visit(constraint, new BooleanFormulaTransformationVisitor(mgr) {});
    assertThatFormula(newConstraint).isUnsatisfiable();
  }

  @Test
  public void testVisitingTrue() throws Exception {

    // Check that "true" is correctly treated as a constant.
    BooleanFormula t = bmgr.makeBoolean(true);
    final List<Boolean> containsTrue = new ArrayList<>();
    mgr.visitRecursively(
        t,
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
        });
    assertThat(containsTrue).isNotEmpty();
  }

  @Test
  public void testCorrectFunctionNames() throws Exception {
    BooleanFormula a = bmgr.makeVariable("a");
    BooleanFormula b = bmgr.makeVariable("b");
    BooleanFormula ab = bmgr.and(a, b);

    final Set<String> found = new HashSet<>();
    mgr.visitRecursively(
        ab,
        new DefaultFormulaVisitor<TraversalProcess>() {

          @Override
          protected TraversalProcess visitDefault(Formula f) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitFunction(
              Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {

            found.add(functionDeclaration.getName());

            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitFreeVariable(Formula f, String name) {
            found.add(name);
            return TraversalProcess.CONTINUE;
          }
        });

    assertThat(found).containsAllOf("a", "b");
    assertThat(found).hasSize(3); // all of the above plus the boolean "and" function
    assertThat(found).doesNotContain(ab.toString());
  }

  @Test
  public void recursiveTransformationVisitorTest() throws Exception {
    BooleanFormula f =
        bmgr.or(
            imgr.equal(
                imgr.add(imgr.makeVariable("x"), imgr.makeVariable("y")), imgr.makeNumber(1)),
            imgr.equal(imgr.makeVariable("z"), imgr.makeNumber(10)));
    BooleanFormula transformed =
        mgr.transformRecursively(
            f,
            new FormulaTransformationVisitor(mgr) {
              @Override
              public Formula visitFreeVariable(Formula f, String name) {
                return mgr.makeVariable(mgr.getFormulaType(f), name + "'");
              }
            });
    assertThatFormula(transformed)
        .isEquivalentTo(
            bmgr.or(
                imgr.equal(
                    imgr.add(imgr.makeVariable("x'"), imgr.makeVariable("y'")), imgr.makeNumber(1)),
                imgr.equal(imgr.makeVariable("z'"), imgr.makeNumber(10))));
  }

  @Test
  public void booleanRecursiveTraversalTest() throws Exception {
    BooleanFormula f =
        bmgr.or(
            bmgr.and(bmgr.makeVariable("x"), bmgr.makeVariable("y")),
            bmgr.and(
                ImmutableList.of(
                    bmgr.makeVariable("z"),
                    bmgr.makeVariable("d"),
                    imgr.equal(imgr.makeVariable("gg"), imgr.makeNumber(5)))));
    final Set<String> foundVars = new HashSet<>();
    bmgr.visitRecursively(
        f,
        new DefaultBooleanFormulaVisitor<TraversalProcess>() {
          @Override
          protected TraversalProcess visitDefault() {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitAtom(
              BooleanFormula atom, FunctionDeclaration<BooleanFormula> funcDecl) {
            if (funcDecl.getKind() == FunctionDeclarationKind.VAR) {
              foundVars.add(funcDecl.getName());
            }
            return TraversalProcess.CONTINUE;
          }
        });
    assertThat(foundVars).containsExactly("x", "y", "z", "d");
  }

  @Test
  public void testTransformationInsideQuantifiers() throws Exception {
    requireQuantifiers();
    // TODO Maybe rewrite using quantified integer variable to allow testing with Princess
    assume()
        .withFailureMessage("Princess does not support quantifier over boolean variables")
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);

    List<BooleanFormula> usedVars =
        ImmutableList.of("a", "b", "c", "d", "e", "f")
            .stream()
            .map(var -> bmgr.makeVariable(var))
            .collect(Collectors.toList());
    Fuzzer fuzzer = new Fuzzer(mgr, new Random(0));
    List<BooleanFormula> quantifiedVars = ImmutableList.of(bmgr.makeVariable("a"));
    BooleanFormula body = fuzzer.fuzz(30, usedVars.toArray(new BooleanFormula[usedVars.size()]));
    BooleanFormula f = qmgr.forall(quantifiedVars, body);
    BooleanFormula transformed =
        bmgr.transformRecursively(
            f,
            new BooleanFormulaTransformationVisitor(mgr) {
              @Override
              public BooleanFormula visitAtom(
                  BooleanFormula pAtom, FunctionDeclaration<BooleanFormula> decl) {
                if (decl.getKind() == FunctionDeclarationKind.VAR) {
                  // Uppercase all variables.
                  return bmgr.makeVariable(decl.getName().toUpperCase());
                } else {
                  return pAtom;
                }
              }
            });
    assertThat(
            mgr.extractVariables(transformed)
                .keySet()
                .stream()
                .allMatch(pS -> pS.equals(pS.toUpperCase())))
        .isTrue();
  }
}
