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

package org.sosy_lab.java_smt.solvers.apron;

import apron.Tcons1;
import apron.Texpr1BinNode;
import apron.Texpr1UnNode;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronRationalType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.FormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronConstraint;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntBinaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatBinaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatCstNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatUnaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatVarNode;

public class ApronRationalFormulaManager extends
                                         ApronNumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {

  private final ApronFormulaCreator formulaCreator;
  private final ApronFormulaType rationalType = new ApronRationalType();

  protected ApronRationalFormulaManager(
      ApronFormulaCreator pFormulaCreator,
      NonLinearArithmetic pNonLinearArithmetic) {
    super(pFormulaCreator, pNonLinearArithmetic);
    this.formulaCreator = pFormulaCreator;
  }

  @Override
  protected FormulaType getNumeralType() {
    return FormulaType.RATIONAL;
  }

  @Override
  protected ApronNode makeNumberImpl(double pNumber) {
    return null;
  }

  @Override
  protected ApronNode makeNumberImpl(BigDecimal pNumber) {
    return null;
  }


  @Override
  protected ApronNode makeVariableImpl(String i) {
    return formulaCreator.makeVariable(rationalType, i);
  }

  protected ApronNode makeNumberImpl(long i) {
    return new ApronRatCstNode(BigInteger.valueOf(i), BigInteger.ONE);
  }

  @Override
  protected ApronNode makeNumberImpl(BigInteger i) {
    return new ApronRatCstNode(i, BigInteger.ONE);
  }

  @Override
  protected ApronNode makeNumberImpl(String i) {
    return new ApronRatCstNode(BigInteger.valueOf(Integer.parseInt(i)), BigInteger.ONE);
  }

  @Override
  protected ApronNode negate(ApronNode pParam1) {
    ApronRatUnaryNode unaryNode = new ApronRatUnaryNode(pParam1,
        Texpr1UnNode.OP_NEG);
    return unaryNode;
  }

  @Override
  protected ApronNode add(ApronNode pParam1, ApronNode pParam2) {
    ApronRatBinaryNode binaryNode = new ApronRatBinaryNode(pParam1, pParam2,
        Texpr1BinNode.OP_ADD);
    return binaryNode;
  }

  @Override
  protected ApronNode sumImpl(List<ApronNode> operands) {
    if(!operands.isEmpty()){
      ApronNode first = operands.remove(0);
      for (ApronNode operand:operands) {
        first = new ApronRatBinaryNode(first, operand,
            Texpr1BinNode.OP_ADD);
      }
      return first;
    }
    return null;  }

  @Override
  protected ApronNode subtract(ApronNode pParam1, ApronNode pParam2) {
    ApronRatBinaryNode binaryNode = new ApronRatBinaryNode(pParam1, pParam2,
        Texpr1BinNode.OP_SUB);
    return binaryNode;
  }

  @Override
  protected ApronNode divide(ApronNode pParam1, ApronNode pParam2) {
    ApronRatBinaryNode binaryNode = new ApronRatBinaryNode(pParam1, pParam2,
        Texpr1BinNode.OP_DIV);
    return binaryNode;
  }

  @Override
  protected ApronNode multiply(ApronNode pParam1, ApronNode pParam2) {
    ApronRatBinaryNode binaryNode = new ApronRatBinaryNode(pParam1, pParam2,
        Texpr1BinNode.OP_MUL);
    return binaryNode;
  }

  @Override
  protected ApronNode equal(ApronNode pParam1, ApronNode pParam2) {
    ApronRatBinaryNode binaryNode = new ApronRatBinaryNode(pParam1, pParam2,
        Texpr1BinNode.OP_SUB);
    ApronConstraint constraint = new ApronConstraint(Tcons1.EQ, formulaCreator.getEnvironment(),
        binaryNode);
    return constraint;
  }

  @Override
  protected ApronNode distinctImpl(List pNumbers) {
    return null;
  }

  @Override
  protected ApronNode greaterThan(ApronNode pParam1, ApronNode pParam2) {
    ApronRatBinaryNode binaryNode = new ApronRatBinaryNode(pParam1, pParam2,
        Texpr1BinNode.OP_SUB);
    ApronConstraint constraint = new ApronConstraint(Tcons1.SUP, formulaCreator.getEnvironment(),
        binaryNode);
    return constraint;
  }

  @Override
  protected ApronNode greaterOrEquals(ApronNode pParam1, ApronNode pParam2) {
    ApronRatBinaryNode binaryNode = new ApronRatBinaryNode(pParam1, pParam2,
        Texpr1BinNode.OP_SUB);
    ApronConstraint constraint = new ApronConstraint(Tcons1.SUPEQ, formulaCreator.getEnvironment(),
        binaryNode);
    return constraint;
  }

  @Override
  protected ApronNode lessThan(ApronNode pParam1, ApronNode pParam2) {
    ApronRatBinaryNode binaryNode = new ApronRatBinaryNode(pParam2, pParam1,
        Texpr1BinNode.OP_SUB);
    ApronConstraint constraint = new ApronConstraint(Tcons1.SUP, formulaCreator.getEnvironment(),
        binaryNode);
    return constraint;
  }

  @Override
  protected ApronNode lessOrEquals(ApronNode pParam1, ApronNode pParam2) {
    ApronRatBinaryNode binaryNode = new ApronRatBinaryNode(pParam2, pParam1,
        Texpr1BinNode.OP_SUB);
    ApronConstraint constraint = new ApronConstraint(Tcons1.SUPEQ, formulaCreator.getEnvironment(),
        binaryNode);
    return constraint;
  }

}
