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
import java.math.BigInteger;
import java.util.Objects;
import org.junit.Test;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.SolverException;

public class SMTLIB2FloatingPointTest extends SolverBasedTest0{
  @Override
  protected Solvers solverToUse() {
    return Solvers.Z3;
  }

  @Test
  public void simpleTestDeclaration() throws
  IOException, SolverException, InterruptedException, InvalidConfigurationException {
    String x = "(declare-const a (_ FloatingPoint 8 24))\n";
    BooleanFormula actualResult = mgr.universalParseFromString(x);
    FloatingPointFormula a = Objects.requireNonNull(fpmgr).makeVariable("a",
        FormulaType.getFloatingPointType(8,
        24));
    assertThat(actualResult.equals(a));
  }
  @Test
  public void testDeclareFloatingPoints()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(assert (fp.eq a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a =
        fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula b =
        fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 24));

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);

    BooleanFormula expectedResult = constraint;
    assertThat(expectedResult.equals(actualResult));
  }

  @Test
  public void testFloatingPointAddition()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a  (_ FloatingPoint 8 24))\n"
            + "(declare-const b  (_ FloatingPoint 8 24))\n"
            + "(declare-const c  (_ FloatingPoint 8 24))\n"
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

    assertThat(expectedResult.equals(actualResult));;
  }

  @Test
  public void testDeclareFloatingPointsWithBitVectors()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 8 24))\n"
            + "(declare-const b (_ FloatingPoint 8 24))\n"
            + "(assert (= a ((_ to_fp 8 24) RNE #b00000000000000000000000000000000)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a = fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 24));

    BigInteger bitvectorValue = new BigInteger("00000000000000000000000000000000", 2);
    if(bitvectorValue.floatValue()!=0) throw new RuntimeException(bitvectorValue.toString());
    FloatingPointFormula b = fpmgr.fromIeeeBitvector(
        bvmgr.makeBitvector(32, bitvectorValue),
        FormulaType.getFloatingPointType(8, 24)
    );

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);
    BooleanFormula expectedResult = constraint;

    assertThat(expectedResult.equals(actualResult));

  }
  @Test
  public void testDeclareFloatingPointsWithHexadecimal()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a  (_ FloatingPoint 8 24))\n"
            + "(declare-const b  (_ FloatingPoint 8 24))\n"
            + "(assert (= a ((_ to_fp 8 24) #x40400000)))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a =
        fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula b =
        fpmgr.fromIeeeBitvector(bvmgr.makeBitvector(32, new BigInteger("0x400000",16)),
            FormulaType.getFloatingPointType(8, 24));
    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);

    BooleanFormula expectedResult = constraint;

    assertThat(expectedResult.equals(actualResult));;
  }
  @Test
  public void testDeclareFloat8()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a (_ FloatingPoint 5 3))\n"
            + "(declare-const b  (_ FloatingPoint 5 3))\n"
            + "(assert (fp.eq a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a =
        fpmgr.makeVariable("a", FormulaType.getFloatingPointType(5, 3));
    FloatingPointFormula b =
        fpmgr.makeVariable("b", FormulaType.getFloatingPointType(5, 3));

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);

    BooleanFormula expectedResult = constraint;

    assertThat(expectedResult.equals(actualResult));;
  }
  @Test
  public void testDeclareFloat16()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a Float16)\n"
            + "(declare-const b Float16)\n"
            + "(assert (fp.eq a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a =
        fpmgr.makeVariable("a", FormulaType.getFloatingPointType(5, 11));
    FloatingPointFormula b =
        fpmgr.makeVariable("b", FormulaType.getFloatingPointType(5, 11));

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);

    BooleanFormula expectedResult = constraint;

    assertThat(expectedResult.equals(actualResult));;
  }
  @Test
  public void testDeclareFloat32()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a Float32)\n"
            + "(declare-const b Float32)\n"
            + "(assert (fp.eq a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a =
        fpmgr.makeVariable("a", FormulaType.getFloatingPointType(8, 24));
    FloatingPointFormula b =
        fpmgr.makeVariable("b", FormulaType.getFloatingPointType(8, 24));

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);

    BooleanFormula expectedResult = constraint;

    assertThat(expectedResult.equals(actualResult));;
  }
  @Test
  public void testDeclareFloat64()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a Float64)\n"
            + "(declare-const b Float64)\n"
            + "(assert (fp.eq a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a =
        fpmgr.makeVariable("a", FormulaType.getFloatingPointType(11, 53));
    FloatingPointFormula b =
        fpmgr.makeVariable("b", FormulaType.getFloatingPointType(11, 53));

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);

    BooleanFormula expectedResult = constraint;

    assertThat(expectedResult.equals(actualResult));;
  }
  @Test
  public void testDeclareFloat128()
      throws IOException, SolverException, InterruptedException, InvalidConfigurationException {

    String x =
        "(declare-const a Float128)\n"
            + "(declare-const b Float128))\n"
            + "(assert (fp.eq a b))\n";

    BooleanFormula actualResult = mgr.universalParseFromString(x);

    FloatingPointFormula a =
        fpmgr.makeVariable("a", FormulaType.getFloatingPointType(15, 113));
    FloatingPointFormula b =
        fpmgr.makeVariable("b", FormulaType.getFloatingPointType(15, 113));

    BooleanFormula constraint = fpmgr.equalWithFPSemantics(a, b);

    BooleanFormula expectedResult = constraint;

    assertThat(expectedResult.equals(actualResult));;
  }
  /*
 Make Test for this :
(
(define-fun a () (_ FloatingPoint 8 24) (fp #b1 #b01111110 #b01010101010101010101011))
(define-fun b () (_ FloatingPoint 8 24) (fp #b1 #b01111110 #b11111111111111111111111))
(define-fun c () (_ FloatingPoint 8 24) (fp #b1 #b01111110 #b11111111111111111111111))
(define-fun rm () RoundingMode roundTowardPositive)
)
(((fp.fma rm a b c) (fp #b1 #b01111101 #b01010101010101010101001)))
(((fp.add rm (fp.mul rm a b) c) (fp #b1 #b01111101 #b01010101010101010101000)))
   */
}
