// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assert_;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.collect.ImmutableList;
import com.google.common.truth.Truth;
import java.util.List;
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

@RunWith(Parameterized.class)
public class UFManagerTest extends SolverBasedTest0 {

  private static final ImmutableList<String> VALID_NAMES = ImmutableList.of("Func", "(Func)");

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
  public void testDeclareAndCallUFWithInt() {
    requireIntegers();
    for (String name : VALID_NAMES) {
      Formula f =
          fmgr.declareAndCallUF(
              name, FormulaType.IntegerType, ImmutableList.of(imgr.makeNumber(1)));
      FunctionDeclaration<?> declaration = getDeclaration(f);
      Truth.assertThat(declaration.getName()).isEqualTo(name);
      Formula f2 = mgr.makeApplication(declaration, imgr.makeNumber(1));
      Truth.assertThat(f2).isEqualTo(f);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  @Test(expected = IllegalArgumentException.class)
  public void testDeclareAndCallUFWithIntWithUnsupportedName() {
    requireIntegers();
    fmgr.declareAndCallUF("|Func|", FormulaType.IntegerType, ImmutableList.of(imgr.makeNumber(1)));
    assert_().fail();
  }

  @Test
  public void testDeclareAndCallUFWithBv() {
    requireBitvectors();
    for (String name : VALID_NAMES) {
      Formula f =
          fmgr.declareAndCallUF(
              name,
              FormulaType.getBitvectorTypeWithSize(4),
              ImmutableList.of(bvmgr.makeBitvector(4, 1)));
      FunctionDeclaration<?> declaration = getDeclaration(f);
      Truth.assertThat(declaration.getName()).isEqualTo(name);
      Formula f2 = mgr.makeApplication(declaration, bvmgr.makeBitvector(4, 1));
      Truth.assertThat(f2).isEqualTo(f);
    }
  }

  @SuppressWarnings("CheckReturnValue")
  @Test(expected = IllegalArgumentException.class)
  public void testDeclareAndCallUFWithBvWithUnsupportedName() {
    requireBitvectors();
    fmgr.declareAndCallUF(
        "|Func|",
        FormulaType.getBitvectorTypeWithSize(4),
        ImmutableList.of(bvmgr.makeBitvector(4, 1)));
    assert_().fail();
  }

  @Test
  public void testDeclareAndCallUFWithTypedArgs() {
    requireBooleanArgument();
    createAndCallUF("fooBool1", FormulaType.BooleanType, bmgr.makeTrue());
    createAndCallUF("fooBool2", FormulaType.BooleanType, bmgr.makeTrue(), bmgr.makeTrue());
    createAndCallUF(
        "fooBool3", FormulaType.IntegerType, bmgr.makeTrue(), bmgr.makeTrue(), bmgr.makeTrue());

    createAndCallUF("fooInt1", FormulaType.IntegerType, imgr.makeNumber(2));
    createAndCallUF("fooInt2", FormulaType.IntegerType, imgr.makeNumber(1), imgr.makeNumber(2));
    createAndCallUF(
        "fooInt3",
        FormulaType.BooleanType,
        imgr.makeNumber(1),
        imgr.makeNumber(2),
        imgr.makeNumber(3));

    createAndCallUF("fooMixed1", FormulaType.IntegerType, bmgr.makeTrue(), imgr.makeNumber(2));
    createAndCallUF(
        "fooMixed2", FormulaType.IntegerType, bmgr.makeTrue(), bmgr.makeTrue(), imgr.makeNumber(2));
    createAndCallUF(
        "fooMixed3", FormulaType.BooleanType, bmgr.makeTrue(), imgr.makeNumber(2), bmgr.makeTrue());
  }

  @Test
  public void testDeclareAndCallUFWithRationalArgs() {
    requireRationals();
    createAndCallUF("fooRat1", FormulaType.RationalType, rmgr.makeNumber(2.5));
    createAndCallUF("fooRat2", FormulaType.IntegerType, rmgr.makeNumber(1.5), rmgr.makeNumber(2.5));
    requireBooleanArgument();
    createAndCallUF(
        "fooMixed3",
        FormulaType.BooleanType,
        bmgr.makeTrue(),
        imgr.makeNumber(2),
        rmgr.makeNumber(3.33));
  }

  @Test
  public void testDeclareAndCallUFWithBVArgs() {
    requireBitvectors();
    createAndCallUF("fooBV1", FormulaType.getBitvectorTypeWithSize(5), bvmgr.makeBitvector(3, 3L));
    requireBooleanArgument();
    createAndCallUF(
        "fooMixedBV1",
        FormulaType.getBitvectorTypeWithSize(5),
        bmgr.makeTrue(),
        imgr.makeNumber(2),
        bvmgr.makeBitvector(3, 3L));
    createAndCallUF(
        "fooMixedBV2",
        FormulaType.BooleanType,
        bmgr.makeTrue(),
        imgr.makeNumber(2),
        bvmgr.makeBitvector(3, 3L));
  }

  private void requireBooleanArgument() {
    assume()
        .withMessage("Solver %s does not support boolean arguments", solverToUse())
        .that(solver)
        .isNotEqualTo(Solvers.MATHSAT5);
  }

  /** utility method: create an UF from given arguments and return type and calls it. */
  private void createAndCallUF(
      String name, FormulaType<? extends Formula> retType, Formula... args) {
    Formula f = fmgr.declareAndCallUF(name, retType, args);
    FunctionDeclaration<?> declaration = getDeclaration(f);
    Truth.assertThat(declaration.getName()).isEqualTo(name);
    Formula f2 = mgr.makeApplication(declaration, args);
    Truth.assertThat(f2).isEqualTo(f);
  }

  private FunctionDeclaration<?> getDeclaration(Formula pFormula) {
    assume()
        .withMessage("Solver %s does not support visiters", solverToUse())
        .that(solver)
        .isNotEqualTo(Solvers.BOOLECTOR);
    return mgr.visit(
        pFormula,
        new ExpectedFormulaVisitor<>() {
          @Override
          public FunctionDeclaration<?> visitFunction(
              Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
            return functionDeclaration;
          }
        });
  }
}
