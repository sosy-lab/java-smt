/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.stp;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.AfterClass;
import org.junit.Ignore;
import org.junit.Test;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class TestStpSolver {

  private final Configuration config;
  private final LogManager logger;
  private final ShutdownNotifier shutdownNotifier;
  private final Solvers solver;

  public static SolverContext context;

  // variables
  BooleanFormula p;
  BooleanFormula q;
  BooleanFormula trueValue;
  BooleanFormula falseValue;

  BitvectorFormula bv8;
  BitvectorFormula bv32;
  BitvectorFormula zero;
  BitvectorFormula two;
  BitvectorFormula twenty;
  BitvectorFormula x;
  BitvectorFormula y;

  ArrayFormula<BitvectorFormula, BitvectorFormula> arrayOfBV8;
  ArrayFormula<BitvectorFormula, BitvectorFormula> arrayOfBV32;

   public TestStpSolver() throws InvalidConfigurationException {
   config = Configuration.defaultConfiguration();
   logger = BasicLogManager.create(config);
   shutdownNotifier = ShutdownNotifier.createDummy();
    solver = Solvers.STP;
    // solver = Solvers.MATHSAT5;

   context = SolverContextFactory.createSolverContext(config, logger, shutdownNotifier, solver);
   }

   @AfterClass
   public static void afterClass() {
     if (context != null) {
       context.close();
     }
   }

  @Test
  public void createBooleanVariables() {

    BooleanFormulaManager boolFmgr = context.getFormulaManager().getBooleanFormulaManager();

    p = boolFmgr.makeVariable("p");
    q = boolFmgr.makeVariable("q");
    trueValue = boolFmgr.makeTrue();
    falseValue = boolFmgr.makeBoolean(false);

    assertTrue(context.getFormulaManager().getFormulaType(p).isBooleanType());
    assertTrue(context.getFormulaManager().getFormulaType(q).isBooleanType());
    assertTrue(context.getFormulaManager().getFormulaType(trueValue).isBooleanType());
    assertTrue(context.getFormulaManager().getFormulaType(falseValue).isBooleanType());

    // these would raise a nasty exception because these are not Values
    // assertTrue(boolFMgr.isFalse(falseVar));
    // assertTrue(boolFMgr.isTrue(trueVar));

    assertTrue(boolFmgr.isTrue(trueValue));
    assertTrue(boolFmgr.isFalse(falseValue));
  }

  @Test
  public void createBitVectorVariables() {

    BitvectorFormulaManager bvFmgr = context.getFormulaManager().getBitvectorFormulaManager();

    bv8 = bvFmgr.makeVariable(8, "bv8");
    bv32 = bvFmgr.makeVariable(32, "bv32");
    x = bvFmgr.makeVariable(8, "x");
    y = bvFmgr.makeVariable(8, "y");

    // these are constants
    zero = bvFmgr.makeBitvector(8, 0);
    two = bvFmgr.makeBitvector(8, 2);
    twenty = bvFmgr.makeBitvector(8, 20);

    assertTrue(context.getFormulaManager().getFormulaType(bv8).isBitvectorType());
    assertTrue(context.getFormulaManager().getFormulaType(bv32).isBitvectorType());
  }


  @Test
  public void createArrayVariables() {

    ArrayFormulaManager arrayFmgr = context.getFormulaManager().getArrayFormulaManager();

    BitvectorType indexType8 = FormulaType.getBitvectorTypeWithSize(8);
    BitvectorType indexType32 = FormulaType.getBitvectorTypeWithSize(32);
    BitvectorType elementType8 = FormulaType.getBitvectorTypeWithSize(8);
    BitvectorType elementType32 = FormulaType.getBitvectorTypeWithSize(32);

    // Same bit size is expected by javaSMT otherwise you get "expected Array by got Array"
    arrayOfBV8 = arrayFmgr.makeArray("array_8", indexType8, elementType8);
    arrayOfBV32 = arrayFmgr.makeArray("array_32", indexType32, elementType32);

    assertTrue(context.getFormulaManager().getFormulaType(arrayOfBV8).isArrayType());
    assertTrue(context.getFormulaManager().getFormulaType(arrayOfBV32).isArrayType());
  }

  @Test
  public void BooleanSimpleFormulaAndToString() {
    BooleanFormulaManager boolFmgr = context.getFormulaManager().getBooleanFormulaManager();

    createBooleanVariables();

    BooleanFormula pAndNotq = boolFmgr.and(p, boolFmgr.not(q));
    BooleanFormula notOf_pAndNotq = boolFmgr.not(pAndNotq);

    assertEquals("p", p.toString().trim());
    assertEquals("q", q.toString().trim());
    assertEquals(boolFmgr.not(pAndNotq).toString(), notOf_pAndNotq.toString());

    // System.out.println("p gives: " + p.toString());
    // System.out.println("q gives: " + q.toString());
    // System.out.println("pAndNotq gives: " + pAndNotq.toString());

  }

  @Ignore
  @Test
  public void BitVectorSimpleFormulaAndToString() throws Exception {
    BitvectorFormulaManager bvFmgr = context.getFormulaManager().getBitvectorFormulaManager();
    createBitVectorVariables();

    BitvectorFormula twoPlusTwo = bvFmgr.add(two, two);
    BitvectorFormula four = bvFmgr.makeBitvector(4, 4);

    // BooleanFormula equalityOf4 = bvFmgr.equal(twoPlusTwo, four);
    // BooleanFormula unEqualityOf4 = bvFmgr.equal(twoPlusTwo, twenty);

    // System.out.println("\"twoPlusTwo\" gives: " + twoPlusTwo.toString());
    // System.out.println("\"four \" gives: " + four.toString());

    // // x + x
    // BitvectorFormula xPlusx = bvFmgr.add(x, x);
    // // x + y
    // BitvectorFormula xPlusy = bvFmgr.add(x, y);
    // // 2*x
    // BitvectorFormula xTimes2 = bvFmgr.multiply(x, two);
    // // x + x = 2*x
    // BooleanFormula equality = bvFmgr.equal(xPlusx, xTimes2);
    // // x + x = 2
    // BooleanFormula badEquality = bvFmgr.equal(xPlusx, two);
    //
    // System.out.println("x gives: " + x.toString());
    // System.out.println("y gives: " + y.toString());
    // System.out.println("two gives: " + two.toString());
    // System.out.println("twenty gives: " + twenty.toString());
    //
    // System.out.println("xPlusx gives: " + xPlusx.toString());
    // System.out.println("xPlusy gives: " + xPlusy.toString());
    // System.out.println("xTimes2 gives: " + xTimes2.toString());
    //
    // System.out.println("equality gives: " + equality.toString());
    // System.out.println("badEquality gives: " + badEquality.toString());

  }

  @Test
  public void BitVectorFormulaHashCode() {
    BitvectorFormulaManager bvFmgr = context.getFormulaManager().getBitvectorFormulaManager();
    createBitVectorVariables();

    BitvectorFormula anotherTwo = bvFmgr.makeBitvector(8, 2);
    BitvectorFormula four = bvFmgr.makeBitvector(8, 4);
    BitvectorFormula anotherFour = bvFmgr.makeBitvector(8, 4);

    assertEquals(two.toString(), anotherTwo.toString());
    assertEquals(four.toString(), anotherFour.toString());
    assertFalse("anotherTwo and two are the same objects", anotherTwo.equals(two));
    assertFalse("anotherFour and four are the same objects", anotherFour.equals(four));
  }

  // @Ignore
  // @Test
  public void ArraySimpleFormulaAndToString() {
    ArrayFormulaManager arrayFmgr = context.getFormulaManager().getArrayFormulaManager();
    BitvectorFormulaManager bvFmgr = context.getFormulaManager().getBitvectorFormulaManager();

    createArrayVariables();
    createBitVectorVariables();

    BitvectorFormula one = bvFmgr.makeBitvector(8, 1);
    BitvectorFormula three = bvFmgr.makeBitvector(8, 3);
    BitvectorFormula four = bvFmgr.makeBitvector(8, 4);

    // arrayOfBV32

    arrayFmgr.store(arrayOfBV8, zero, four);// TODO fix Error
    arrayFmgr.store(arrayOfBV8, one, three);// TODO fix Error

    System.out.println("arrayOfBV8 : " + arrayOfBV8.toString());
    // assertEquals("p", p.toString().trim());
    // assertEquals("q", q.toString().trim());
    // assertEquals(boolFmgr.not(pAndNotq).toString(), notOf_pAndNotq.toString());

    // System.out.println("p gives: " + p.toString());
    // System.out.println("q gives: " + q.toString());
    // System.out.println("pAndNotq gives: " + pAndNotq.toString());

  }


  @Test
  public void ProofBooleanFormula() throws InterruptedException, SolverException {
    BooleanFormulaManager boolFmgr = context.getFormulaManager().getBooleanFormulaManager();

    // create atoms
    BooleanFormula xL = boolFmgr.makeVariable("xL");
    BooleanFormula xH = boolFmgr.makeVariable("xH");
    BooleanFormula yL = boolFmgr.makeVariable("yL");
    BooleanFormula yH = boolFmgr.makeVariable("yH");

    // create formula
    BooleanFormula lowXOR = boolFmgr.xor(xL, yL);
    BooleanFormula highXOR = boolFmgr.xor(xH, yH);
    BooleanFormula twoBitAdder = boolFmgr.and(lowXOR, highXOR); // Formula to solve

//    try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
    ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS);
      boolean isUnsat;

      prover.push();
      prover.addConstraint(twoBitAdder);
      prover.push();

      isUnsat = prover.isUnsat();
      assert !isUnsat;
      // try (Model model = prover.getModel()) {
      System.out.println("SAT : 2-bit Adder ");
      // }
//    }
    // prover.close();
  }

  // test getModel on formulae (Bool, BV, Array)

  // Test Prover

}
