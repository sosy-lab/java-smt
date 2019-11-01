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
package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.collect.ImmutableList;
import com.google.common.truth.Truth;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.stream.Stream;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
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

  /** visit a formula and fail on OTHER, i.e., unexpected function declaration type. */
  private final class FunctionDeclarationVisitor extends DefaultFormulaVisitor<Formula> {

    private final List<FunctionDeclarationKind> found = new ArrayList<>();

    @Override
    public Formula visitFunction(
        Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
      found.add(functionDeclaration.getKind());
      Truth.assert_()
          .withMessage(
              "unexpected declaration kind '%s' in function '%s' with args '%s'.",
              functionDeclaration, f, args)
          .that(functionDeclaration.getKind())
          .isNotEqualTo(FunctionDeclarationKind.OTHER);
      for (Formula arg : args) {
        mgr.visit(arg, this);
      }
      return visitDefault(f);
    }

    @Override
    protected Formula visitDefault(Formula pF) {
      return pF;
    }
  }

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
  public void bitvectorIdVisit() {
    requireBitvectors();
    BitvectorType bv8 = FormulaType.getBitvectorTypeWithSize(8);
    BitvectorFormula x = bvmgr.makeVariable(bv8, "x");
    BitvectorFormula y = bvmgr.makeVariable(bv8, "y");

    for (Formula f :
        ImmutableList.of(
            bvmgr.equal(x, y),
            bvmgr.add(x, y),
            bvmgr.subtract(x, y),
            bvmgr.multiply(x, y),
            bvmgr.and(x, y),
            bvmgr.or(x, y),
            bvmgr.xor(x, y),
            bvmgr.lessThan(x, y, true),
            bvmgr.lessThan(x, y, false),
            bvmgr.lessOrEquals(x, y, true),
            bvmgr.lessOrEquals(x, y, false),
            bvmgr.greaterThan(x, y, true),
            bvmgr.greaterThan(x, y, false),
            bvmgr.greaterOrEquals(x, y, true),
            bvmgr.greaterOrEquals(x, y, false),
            bvmgr.divide(x, y, true),
            bvmgr.divide(x, y, false),
            bvmgr.modulo(x, y, true),
            bvmgr.modulo(x, y, false),
            bvmgr.not(x),
            bvmgr.negate(x),
            bvmgr.extract(x, 7, 5, true),
            bvmgr.extract(x, 7, 5, false),
            bvmgr.concat(x, y))) {
      mgr.visit(f, new FunctionDeclarationVisitor());
    }
  }

  @Test
  public void floatIdVisit() {
    requireFloats();
    FloatingPointType fp = FormulaType.getSinglePrecisionFloatingPointType();
    FloatingPointFormula x = fpmgr.makeVariable("x", fp);
    FloatingPointFormula y = fpmgr.makeVariable("y", fp);

    for (Formula f :
        ImmutableList.of(
            fpmgr.equalWithFPSemantics(x, y),
            fpmgr.add(x, y),
            fpmgr.subtract(x, y),
            fpmgr.multiply(x, y),
            fpmgr.lessThan(x, y),
            fpmgr.lessOrEquals(x, y),
            fpmgr.greaterThan(x, y),
            fpmgr.greaterOrEquals(x, y),
            fpmgr.divide(x, y),
            fpmgr.round(x, FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN),
            // fpmgr.round(x, FloatingPointRoundingMode.NEAREST_TIES_AWAY),
            fpmgr.round(x, FloatingPointRoundingMode.TOWARD_POSITIVE),
            fpmgr.round(x, FloatingPointRoundingMode.TOWARD_NEGATIVE),
            fpmgr.round(x, FloatingPointRoundingMode.TOWARD_ZERO))) {
      mgr.visit(f, new FunctionDeclarationVisitor());
    }
  }

  @Test
  public void floatMoreVisit() {
    requireFloats();
    requireBitvectors();
    FloatingPointType fp = FormulaType.getSinglePrecisionFloatingPointType();
    FloatingPointFormula x = fpmgr.makeVariable("x", fp);
    BitvectorFormula z = bvmgr.makeVariable(32, "z");

    checkKind(
        fpmgr.castTo(x, FormulaType.getBitvectorTypeWithSize(32)),
        FunctionDeclarationKind.FP_CASTTO_SBV);
    checkKind(
        fpmgr.castTo(x, FormulaType.getDoublePrecisionFloatingPointType()),
        FunctionDeclarationKind.FP_CASTTO_FP);
    checkKind(fpmgr.isNaN(x), FunctionDeclarationKind.FP_IS_NAN);
    checkKind(fpmgr.isNegative(x), FunctionDeclarationKind.FP_IS_NEGATIVE);
    checkKind(fpmgr.isInfinity(x), FunctionDeclarationKind.FP_IS_INF);
    checkKind(fpmgr.isNormal(x), FunctionDeclarationKind.FP_IS_NORMAL);
    checkKind(fpmgr.isSubnormal(x), FunctionDeclarationKind.FP_IS_SUBNORMAL);
    checkKind(fpmgr.isZero(x), FunctionDeclarationKind.FP_IS_ZERO);
    if (Solvers.CVC4 != solverToUse()) { // CVC4 does not support this operation
      checkKind(fpmgr.toIeeeBitvector(x), FunctionDeclarationKind.FP_AS_IEEEBV);
    }
    checkKind(
        fpmgr.castFrom(z, true, FormulaType.getSinglePrecisionFloatingPointType()),
        FunctionDeclarationKind.BV_SCASTTO_FP);
    checkKind(
        fpmgr.castFrom(z, false, FormulaType.getSinglePrecisionFloatingPointType()),
        FunctionDeclarationKind.BV_UCASTTO_FP);
  }

  @Test
  public void bvVisit() {
    requireBitvectors();
    BitvectorFormula x = bvmgr.makeVariable(5, "x");

    for (Formula f : ImmutableList.of(bvmgr.extend(x, 10, true), bvmgr.extend(x, 10, false))) {
      mgr.visit(f, new FunctionDeclarationVisitor());
    }
  }

  private void checkKind(Formula f, FunctionDeclarationKind expected) {
    FunctionDeclarationVisitor visitor = new FunctionDeclarationVisitor();
    mgr.visit(f, visitor);
    Truth.assert_()
        .withMessage(
            "declaration kind '%s' in function '%s' not available, only found '%s'.",
            expected, f, visitor.found)
        .that(visitor.found)
        .contains(expected);
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
          protected TraversalProcess visitDefault(Formula formula) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitFreeVariable(Formula formula, String name) {
            usedVariables.add(name);
            return TraversalProcess.CONTINUE;
          }
        };
    mgr.visitRecursively(f, nameExtractor);
    assertThat(usedVariables).containsExactly("x", "y", "z");
  }

  @Test
  public void testBooleanFormulaQuantifierHandling() throws Exception {
    requireQuantifiers();
    // TODO Maybe rewrite using quantified integer variable to allow testing with Princess
    assume()
        .withMessage("Princess does not support quantifier over boolean variables")
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
  public void testVisitingTrue() {

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
  public void testCorrectFunctionNames() {
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

    assertThat(found).containsAtLeast("a", "b");
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
              public Formula visitFreeVariable(Formula formula, String name) {
                return mgr.makeVariable(mgr.getFormulaType(formula), name + "'");
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
  public void recursiveTransformationVisitorTest2() throws Exception {
    BooleanFormula f = imgr.equal(imgr.makeVariable("y"), imgr.makeNumber(1));
    BooleanFormula transformed =
        mgr.transformRecursively(
            f,
            new FormulaTransformationVisitor(mgr) {
              @Override
              public Formula visitFreeVariable(Formula formula, String name) {
                return mgr.makeVariable(mgr.getFormulaType(formula), name + "'");
              }
            });
    assertThatFormula(transformed)
        .isEquivalentTo(imgr.equal(imgr.makeVariable("y'"), imgr.makeNumber(1)));
  }

  @Test
  public void booleanRecursiveTraversalTest() {
    BooleanFormula f =
        bmgr.or(
            bmgr.and(bmgr.makeVariable("x"), bmgr.makeVariable("y")),
            bmgr.and(
                bmgr.makeVariable("z"),
                bmgr.makeVariable("d"),
                imgr.equal(imgr.makeVariable("gg"), imgr.makeNumber(5))));
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
  public void testTransformationInsideQuantifiers() {
    requireQuantifiers();
    // TODO Maybe rewrite using quantified integer variable to allow testing with Princess
    assume()
        .withMessage("Princess does not support quantifier over boolean variables")
        .that(solverToUse())
        .isNotEqualTo(Solvers.PRINCESS);

    BooleanFormula[] usedVars =
        Stream.of("a", "b", "c", "d", "e", "f")
            .map(var -> bmgr.makeVariable(var))
            .toArray(BooleanFormula[]::new);
    Fuzzer fuzzer = new Fuzzer(mgr, new Random(0));
    List<BooleanFormula> quantifiedVars = ImmutableList.of(bmgr.makeVariable("a"));
    BooleanFormula body = fuzzer.fuzz(30, usedVars);
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

  @Test
  public void extractionTest1() {
    IntegerFormula v = imgr.makeVariable("v");
    BooleanFormula q = fmgr.declareAndCallUF("q", FormulaType.BooleanType, v);
    Map<String, Formula> mapping = mgr.extractVariablesAndUFs(q);
    assertThat(mapping).containsEntry("v", v);
    assertThat(mapping).containsEntry("q", q);
  }

  @Test
  public void extractionTest2() {
    // the same than above, but with nullary UF.
    IntegerFormula v = fmgr.declareAndCallUF("v", FormulaType.IntegerType);
    BooleanFormula q = fmgr.declareAndCallUF("q", FormulaType.BooleanType, v);
    Map<String, Formula> mapping = mgr.extractVariablesAndUFs(q);
    Map<String, Formula> mapping2 = mgr.extractVariables(q);

    // all solvers must provide all symbols
    assertThat(mapping).hasSize(2);
    assertThat(mapping).containsEntry("v", v);
    assertThat(mapping).containsEntry("q", q);

    // some solvers distinguish between nullary UFs and variables and do not provide variables
    if (ImmutableList.of(Solvers.CVC4, Solvers.PRINCESS).contains(solverToUse())) {
      assertThat(mapping2).isEmpty();
    } else {
      assertThat(mapping2).hasSize(1);
      assertThat(mapping2).containsEntry("v", v);
    }
  }
}
