// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.TruthJUnit.assume;
import static org.sosy_lab.java_smt.api.FormulaType.BooleanType;
import static org.sosy_lab.java_smt.api.FormulaType.IntegerType;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.testing.EqualsTester;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Map;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.SolverException;

public class FormulaManagerTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  @Test
  public void testEmptySubstitution() throws SolverException, InterruptedException {
    requireSubstitution();
    requireIntegers();
    assume().withMessage("Princess fails").that(solver).isNotEqualTo(Solvers.PRINCESS);

    IntegerFormula variable1 = imgr.makeVariable("variable1");
    IntegerFormula variable2 = imgr.makeVariable("variable2");
    IntegerFormula variable3 = imgr.makeVariable("variable3");
    IntegerFormula variable4 = imgr.makeVariable("variable4");

    FunctionDeclaration<BooleanFormula> uf2Decl =
        fmgr.declareUF("uf", BooleanType, IntegerType, IntegerType);
    BooleanFormula f1 = fmgr.callUF(uf2Decl, variable1, variable3);
    BooleanFormula f2 = fmgr.callUF(uf2Decl, variable2, variable4);
    BooleanFormula input = bmgr.xor(f1, f2);

    BooleanFormula out = mgr.substitute(input, ImmutableMap.of());
    assertThatFormula(out).isEquivalentTo(input);
  }

  @Test
  public void testNoSubstitution() throws SolverException, InterruptedException {
    requireSubstitution();
    requireIntegers();
    assume().withMessage("Princess fails").that(solver).isNotEqualTo(Solvers.PRINCESS);

    IntegerFormula variable1 = imgr.makeVariable("variable1");
    IntegerFormula variable2 = imgr.makeVariable("variable2");
    IntegerFormula variable3 = imgr.makeVariable("variable3");
    IntegerFormula variable4 = imgr.makeVariable("variable4");

    FunctionDeclaration<BooleanFormula> uf2Decl =
        fmgr.declareUF("uf", BooleanType, IntegerType, IntegerType);
    BooleanFormula f1 = fmgr.callUF(uf2Decl, variable1, variable3);
    BooleanFormula f2 = fmgr.callUF(uf2Decl, variable2, variable4);
    BooleanFormula input = bmgr.xor(f1, f2);

    Map<BooleanFormula, BooleanFormula> substitution =
        ImmutableMap.of(
            bmgr.makeVariable("a"), bmgr.makeVariable("a1"),
            bmgr.makeVariable("b"), bmgr.makeVariable("b1"),
            bmgr.and(bmgr.makeVariable("c"), bmgr.makeVariable("d")), bmgr.makeVariable("e"));

    BooleanFormula out = mgr.substitute(input, substitution);
    assertThatFormula(out).isEquivalentTo(input);
  }

  @Test
  public void testSubstitution() throws SolverException, InterruptedException {
    requireSubstitution();

    BooleanFormula input =
        bmgr.or(
            bmgr.and(bmgr.makeVariable("a"), bmgr.makeVariable("b")),
            bmgr.and(bmgr.makeVariable("c"), bmgr.makeVariable("d")));
    BooleanFormula out =
        mgr.substitute(
            input,
            ImmutableMap.of(
                bmgr.makeVariable("a"), bmgr.makeVariable("a1"),
                bmgr.makeVariable("b"), bmgr.makeVariable("b1"),
                bmgr.and(bmgr.makeVariable("c"), bmgr.makeVariable("d")), bmgr.makeVariable("e")));
    assertThatFormula(out)
        .isEquivalentTo(
            bmgr.or(
                bmgr.and(bmgr.makeVariable("a1"), bmgr.makeVariable("b1")),
                bmgr.makeVariable("e")));
  }

  @Test
  public void testSubstitutionTwice() throws SolverException, InterruptedException {
    requireSubstitution();

    BooleanFormula input =
        bmgr.or(
            bmgr.and(bmgr.makeVariable("a"), bmgr.makeVariable("b")),
            bmgr.and(bmgr.makeVariable("c"), bmgr.makeVariable("d")));
    ImmutableMap<BooleanFormula, BooleanFormula> substitution =
        ImmutableMap.of(
            bmgr.makeVariable("a"), bmgr.makeVariable("a1"),
            bmgr.makeVariable("b"), bmgr.makeVariable("b1"),
            bmgr.and(bmgr.makeVariable("c"), bmgr.makeVariable("d")), bmgr.makeVariable("e"));
    BooleanFormula out = mgr.substitute(input, substitution);
    assertThatFormula(out)
        .isEquivalentTo(
            bmgr.or(
                bmgr.and(bmgr.makeVariable("a1"), bmgr.makeVariable("b1")),
                bmgr.makeVariable("e")));

    BooleanFormula out2 = mgr.substitute(out, substitution);
    assertThatFormula(out2).isEquivalentTo(out);
  }

  @Test
  public void testSubstitutionMultipleInstances() throws SolverException, InterruptedException {
    requireSubstitution();
    requireIntegers();

    IntegerFormula a = imgr.makeVariable("a");
    IntegerFormula b = imgr.makeVariable("b");
    IntegerFormula num12 = imgr.makeNumber(12);
    BooleanFormula input = imgr.lessThan(num12, imgr.add(imgr.add(imgr.add(a, a), a), b));

    ImmutableMap<IntegerFormula, IntegerFormula> substitution = ImmutableMap.of(a, b);
    BooleanFormula out = mgr.substitute(input, substitution);
    assertThatFormula(out)
        .isEquivalentTo(imgr.lessThan(num12, imgr.add(imgr.add(imgr.add(b, b), b), b)));

    BooleanFormula out2 = mgr.substitute(out, substitution);
    assertThatFormula(out2).isEquivalentTo(out);
  }

  @Test
  public void testSubstitutionSelfReference() throws SolverException, InterruptedException {
    requireSubstitution();
    requireIntegers();

    IntegerFormula a = imgr.makeVariable("a");
    IntegerFormula num1 = imgr.makeNumber(1);
    IntegerFormula incremented = imgr.add(a, num1);
    BooleanFormula input = imgr.lessThan(num1, a);

    ImmutableMap<IntegerFormula, IntegerFormula> substitution = ImmutableMap.of(a, incremented);
    BooleanFormula out1 = mgr.substitute(input, substitution);
    assertThatFormula(out1).isEquivalentTo(imgr.lessThan(num1, imgr.add(a, num1)));

    BooleanFormula out2 = mgr.substitute(out1, substitution);
    assertThatFormula(out2).isEquivalentTo(imgr.lessThan(num1, imgr.add(imgr.add(a, num1), num1)));

    BooleanFormula out3 = mgr.substitute(out2, substitution);
    assertThatFormula(out3)
        .isEquivalentTo(imgr.lessThan(num1, imgr.add(imgr.add(imgr.add(a, num1), num1), num1)));

    BooleanFormula out4 = mgr.substitute(out3, substitution);
    assertThatFormula(out4)
        .isEquivalentTo(
            imgr.lessThan(num1, imgr.add(imgr.add(imgr.add(imgr.add(a, num1), num1), num1), num1)));
  }

  @Test
  public void formulaEqualsAndHashCode() {
    requireIntegers();

    // Solvers without integers (Boolector) get their own test below
    assume().that(solverToUse()).isNotEqualTo(Solvers.BOOLECTOR);
    FunctionDeclaration<IntegerFormula> fb = fmgr.declareUF("f_b", IntegerType, IntegerType);

    new EqualsTester()
        .addEqualityGroup(bmgr.makeBoolean(true))
        .addEqualityGroup(bmgr.makeBoolean(false))
        .addEqualityGroup(bmgr.makeVariable("bool_a"))
        .addEqualityGroup(imgr.makeVariable("int_a"))

        // Way of creating numbers should not make a difference.
        .addEqualityGroup(
            imgr.makeNumber(0.0),
            imgr.makeNumber(0L),
            imgr.makeNumber(BigInteger.ZERO),
            imgr.makeNumber(BigDecimal.ZERO),
            imgr.makeNumber("0"))
        .addEqualityGroup(
            imgr.makeNumber(1.0),
            imgr.makeNumber(1L),
            imgr.makeNumber(BigInteger.ONE),
            imgr.makeNumber(BigDecimal.ONE),
            imgr.makeNumber("1"))

        // The same formula when created twice should compare equal.
        .addEqualityGroup(bmgr.makeVariable("bool_b"), bmgr.makeVariable("bool_b"))
        .addEqualityGroup(
            bmgr.and(bmgr.makeVariable("bool_a"), bmgr.makeVariable("bool_b")),
            bmgr.and(bmgr.makeVariable("bool_a"), bmgr.makeVariable("bool_b")))
        .addEqualityGroup(
            imgr.equal(imgr.makeNumber(0), imgr.makeVariable("int_a")),
            imgr.equal(imgr.makeNumber(0), imgr.makeVariable("int_a")))

        // UninterpretedFunctionDeclarations should not compare equal to Formulas,
        // but declaring one twice needs to return the same UIF.
        .addEqualityGroup(
            fmgr.declareUF("f_a", IntegerType, IntegerType),
            fmgr.declareUF("f_a", IntegerType, IntegerType))
        .addEqualityGroup(fb)
        .addEqualityGroup(fmgr.callUF(fb, imgr.makeNumber(0)))
        .addEqualityGroup(fmgr.callUF(fb, imgr.makeNumber(1)), fmgr.callUF(fb, imgr.makeNumber(1)))
        .testEquals();
  }

  @Test
  public void bitvectorFormulaEqualsAndHashCode() {
    // Boolector does not support integers, and it is easier to make a new test with bvs
    requireBitvectors();
    FunctionDeclaration<BitvectorFormula> fb =
        fmgr.declareUF(
            "f_bv",
            FormulaType.getBitvectorTypeWithSize(8),
            FormulaType.getBitvectorTypeWithSize(8));

    new EqualsTester()
        .addEqualityGroup(bmgr.makeBoolean(true))
        .addEqualityGroup(bmgr.makeBoolean(false))
        .addEqualityGroup(bmgr.makeVariable("bool_a"))
        .addEqualityGroup(bvmgr.makeVariable(8, "bv_a"))

        // Way of creating numbers should not make a difference.
        .addEqualityGroup(
            bvmgr.makeBitvector(8, 0L),
            bvmgr.makeBitvector(8, 0),
            bvmgr.makeBitvector(8, BigInteger.ZERO))
        .addEqualityGroup(
            bvmgr.makeBitvector(8, 1L),
            bvmgr.makeBitvector(8, 1),
            bvmgr.makeBitvector(8, BigInteger.ONE))
        // The same formula when created twice should compare equal.
        .addEqualityGroup(bmgr.makeVariable("bool_b"), bmgr.makeVariable("bool_b"))
        .addEqualityGroup(
            bmgr.and(bmgr.makeVariable("bool_a"), bmgr.makeVariable("bool_b")),
            bmgr.and(bmgr.makeVariable("bool_a"), bmgr.makeVariable("bool_b")))
        .addEqualityGroup(
            bvmgr.equal(bvmgr.makeBitvector(8, 0), bvmgr.makeVariable(8, "int_a")),
            bvmgr.equal(bvmgr.makeBitvector(8, 0), bvmgr.makeVariable(8, "int_a")))

        // UninterpretedFunctionDeclarations should not compare equal to Formulas,
        // but declaring one twice needs to return the same UIF.
        .addEqualityGroup(
            fmgr.declareUF(
                "f_a",
                FormulaType.getBitvectorTypeWithSize(8),
                FormulaType.getBitvectorTypeWithSize(8)),
            fmgr.declareUF(
                "f_a",
                FormulaType.getBitvectorTypeWithSize(8),
                FormulaType.getBitvectorTypeWithSize(8)))
        .addEqualityGroup(fb)
        .addEqualityGroup(fmgr.callUF(fb, bvmgr.makeBitvector(8, 0)))
        .addEqualityGroup(
            fmgr.callUF(fb, bvmgr.makeBitvector(8, 1)), // why not equal?!
            fmgr.callUF(fb, bvmgr.makeBitvector(8, 1)))
        .testEquals();
  }

  @Test
  public void variableNameExtractorTest() {
    // Since Boolector does not support integers we use bitvectors
    if (imgr != null) {
      BooleanFormula constr =
          bmgr.or(
              imgr.equal(
                  imgr.subtract(
                      imgr.add(imgr.makeVariable("x"), imgr.makeVariable("z")),
                      imgr.makeNumber(10)),
                  imgr.makeVariable("y")),
              imgr.equal(imgr.makeVariable("xx"), imgr.makeVariable("zz")));
      assertThat(mgr.extractVariables(constr).keySet()).containsExactly("x", "y", "z", "xx", "zz");
      assertThat(mgr.extractVariablesAndUFs(constr)).isEqualTo(mgr.extractVariables(constr));
    } else {
      BooleanFormula bvConstr =
          bmgr.or(
              bvmgr.equal(
                  bvmgr.subtract(
                      bvmgr.add(bvmgr.makeVariable(8, "x"), bvmgr.makeVariable(8, "z")),
                      bvmgr.makeBitvector(8, 10)),
                  bvmgr.makeVariable(8, "y")),
              bvmgr.equal(bvmgr.makeVariable(8, "xx"), bvmgr.makeVariable(8, "zz")));

      requireVisitor();

      assertThat(mgr.extractVariables(bvConstr).keySet())
          .containsExactly("x", "y", "z", "xx", "zz");
      assertThat(mgr.extractVariablesAndUFs(bvConstr)).isEqualTo(mgr.extractVariables(bvConstr));
    }
  }

  @Test
  public void ufNameExtractorTest() {
    // Since Boolector does not support integers we use bitvectors for constraints
    if (imgr != null) {
      BooleanFormula constraint =
          imgr.equal(
              fmgr.declareAndCallUF("uf1", IntegerType, ImmutableList.of(imgr.makeVariable("x"))),
              fmgr.declareAndCallUF("uf2", IntegerType, ImmutableList.of(imgr.makeVariable("y"))));
      assertThat(mgr.extractVariablesAndUFs(constraint).keySet())
          .containsExactly("uf1", "uf2", "x", "y");

      assertThat(mgr.extractVariables(constraint).keySet()).containsExactly("x", "y");
    } else {
      BooleanFormula bvConstraint =
          bvmgr.equal(
              fmgr.declareAndCallUF(
                  "uf1",
                  FormulaType.getBitvectorTypeWithSize(8),
                  ImmutableList.of(bvmgr.makeVariable(8, "x"))),
              fmgr.declareAndCallUF(
                  "uf2",
                  FormulaType.getBitvectorTypeWithSize(8),
                  ImmutableList.of(bvmgr.makeVariable(8, "y"))));

      requireVisitor();

      assertThat(mgr.extractVariablesAndUFs(bvConstraint).keySet())
          .containsExactly("uf1", "uf2", "x", "y");

      assertThat(mgr.extractVariables(bvConstraint).keySet()).containsExactly("x", "y");
    }
  }

  @Test
  public void simplifyIntTest() throws SolverException, InterruptedException {
    requireIntegers();
    // x=1 && y=x+2 && z=y+3 --> simplified: x=1 && y=3 && z=6
    IntegerFormula num1 = imgr.makeNumber(1);
    IntegerFormula num2 = imgr.makeNumber(2);
    IntegerFormula num3 = imgr.makeNumber(3);
    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula y = imgr.makeVariable("y");
    IntegerFormula z = imgr.makeVariable("z");
    BooleanFormula f =
        bmgr.and(
            imgr.equal(x, num1),
            imgr.equal(y, imgr.add(x, num2)),
            imgr.equal(z, imgr.add(y, num3)));
    assertThatFormula(mgr.simplify(f)).isEquisatisfiableTo(f);
  }

  @Test
  public void simplifyBVTest() throws SolverException, InterruptedException {
    requireBitvectors();
    // x=1 && y=x+2 && z=y+3 --> simplified: x=1 && y=3 && z=6
    BitvectorFormula num1 = bvmgr.makeBitvector(4, 1);
    BitvectorFormula num2 = bvmgr.makeBitvector(4, 2);
    BitvectorFormula num3 = bvmgr.makeBitvector(4, 3);
    BitvectorFormula x = bvmgr.makeVariable(4, "x");
    BitvectorFormula y = bvmgr.makeVariable(4, "y");
    BitvectorFormula z = bvmgr.makeVariable(4, "z");
    BooleanFormula f =
        bmgr.and(
            bvmgr.equal(x, num1),
            bvmgr.equal(y, bvmgr.add(x, num2)),
            bvmgr.equal(z, bvmgr.add(y, num3)));
    assertThatFormula(mgr.simplify(f)).isEquisatisfiableTo(f);
  }

  @Test
  public void simplifyArrayTest() throws SolverException, InterruptedException {
    requireIntegers();
    requireArrays();
    // exists arr : (arr[0]=5 && x=arr[0]) --> simplified: x=5
    ArrayFormula<IntegerFormula, IntegerFormula> arr =
        amgr.makeArray("arr", FormulaType.getArrayType(IntegerType, IntegerType));
    IntegerFormula index = imgr.makeNumber(0);
    IntegerFormula value = imgr.makeNumber(5);
    IntegerFormula x = imgr.makeVariable("x");
    ArrayFormula<IntegerFormula, IntegerFormula> write = amgr.store(arr, index, value);
    IntegerFormula read = amgr.select(write, index);
    BooleanFormula f = imgr.equal(x, read);
    assertThatFormula(mgr.simplify(f)).isEquisatisfiableTo(f);
  }
}
