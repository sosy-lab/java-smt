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
import java.util.List;
import org.checkerframework.checker.units.qual.A;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronIntegerType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.FormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronConstraint;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntBinaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntCstNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntUnaryNode;

public class ApronIntegerFormulaManager
    extends ApronNumeralFormulaManager<IntegerFormula, IntegerFormula> implements
                                                                       IntegerFormulaManager {

  private final ApronFormulaType integerType = new ApronIntegerType();
  private final ApronFormulaCreator formulaCreator;

  protected ApronIntegerFormulaManager(
      ApronFormulaCreator pCreator,
      NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
    this.formulaCreator = pCreator;
  }

  @Override
  protected FormulaType getNumeralType() {
    return FormulaType.INTEGER;
  }

  protected ApronNode makeNumberImpl(double pNumber) {
    return new ApronIntCstNode(BigInteger.valueOf((int) pNumber));
  }

  @Override
  protected ApronNode makeNumberImpl(BigDecimal pNumber) {
    return new ApronIntCstNode(pNumber.toBigInteger());
  }

  @Override
  public BooleanFormula modularCongruence(
      IntegerFormula number1,
      IntegerFormula number2,
      BigInteger n) {
    return null;
  }

  @Override
  public BooleanFormula modularCongruence(IntegerFormula number1, IntegerFormula number2, long n) {
    ApronIntCstNode mod = new ApronIntCstNode(BigInteger.valueOf(n));
    ApronIntBinaryNode x = new ApronIntBinaryNode(ApronFormulaManager.getTerm(number1), ApronFormulaManager.getTerm(number2), Texpr1BinNode.OP_SUB);

    if(BigInteger.ZERO.compareTo(BigInteger.valueOf(n))<0){

      return (BooleanFormula) equal(mod,(ApronNode) x);
    }
    return (BooleanFormula) equal((ApronNode) mod,mod);
  }

  @Override
  public IntegerFormula modulo(IntegerFormula numerator, IntegerFormula denumerator) {
    ApronNode node1 = (ApronNode) numerator;
    ApronNode node2 = (ApronNode) denumerator;
    ApronIntBinaryNode result = new ApronIntBinaryNode(node1, node2,
        Texpr1BinNode.OP_MOD);
    return result;
  }


  @Override
  protected ApronNode makeVariableImpl(String i) {
    return this.formulaCreator.makeVariable(integerType, i);
  }

  protected ApronNode makeNumberImpl(long i) {
    return new ApronIntCstNode(BigInteger.valueOf(i));
  }

  @Override
  protected ApronNode makeNumberImpl(BigInteger i) {
    return new ApronIntCstNode(i);
  }

  @Override
  protected ApronNode makeNumberImpl(String i) {
    return new ApronIntCstNode(BigInteger.valueOf(Integer.parseInt(i)));
  }

  @Override
  protected ApronNode negate(ApronNode pParam1) {
    ApronIntUnaryNode unaryNode = new ApronIntUnaryNode(pParam1,
        Texpr1UnNode.OP_NEG);
    return unaryNode;
  }

  @Override
  protected ApronNode add(ApronNode pParam1, ApronNode pParam2) {
    ApronIntBinaryNode binaryNode = new ApronIntBinaryNode(pParam1, pParam2,
        Texpr1BinNode.OP_ADD);
    return binaryNode;
  }

  @Override
  protected ApronNode sumImpl(List<ApronNode> operands) {
    if(!operands.isEmpty()){
    ApronNode first = operands.remove(0);
    for (ApronNode operand:operands) {
      first = new ApronIntBinaryNode(first, operand,
          Texpr1BinNode.OP_ADD);
    }
    return first;
    }
    return null;
  }

  @Override
  protected ApronNode subtract(ApronNode pParam1, ApronNode pParam2) {
    ApronIntBinaryNode binaryNode = new ApronIntBinaryNode(pParam1, pParam2,
        Texpr1BinNode.OP_SUB);
    return binaryNode;
  }

  @Override
  protected ApronNode divide(ApronNode pParam1, ApronNode pParam2) {
    ApronIntBinaryNode binaryNode = new ApronIntBinaryNode(pParam1, pParam2,
        Texpr1BinNode.OP_DIV);
    return binaryNode;
  }

  @Override
  protected ApronNode multiply(ApronNode pParam1, ApronNode pParam2) {
    ApronIntBinaryNode binaryNode = new ApronIntBinaryNode(pParam1, pParam2,
        Texpr1BinNode.OP_MUL);
    return binaryNode;
  }

  @Override
  protected ApronNode equal(ApronNode pParam1, ApronNode pParam2) {
    ApronIntBinaryNode binaryNode = new ApronIntBinaryNode(pParam1, pParam2,
        Texpr1BinNode.OP_SUB);
    ApronConstraint constraint = new ApronConstraint(Tcons1.EQ, formulaCreator.getEnvironment(),
        binaryNode);
    return constraint;
  }

  @Override
  protected ApronNode distinctImpl(List pNumbers) {
    throw new UnsupportedOperationException("Apron does not support distinctImpl()");
  }

  @Override
  protected ApronNode greaterThan(ApronNode pParam1, ApronNode pParam2) {
    ApronIntBinaryNode binaryNode = new ApronIntBinaryNode(pParam1, pParam2,
        Texpr1BinNode.OP_SUB);
    ApronConstraint constraint = new ApronConstraint(Tcons1.SUP, formulaCreator.getEnvironment(),
        binaryNode);
    return constraint;
  }

  @Override
  protected ApronNode greaterOrEquals(ApronNode pParam1, ApronNode pParam2) {
    ApronIntBinaryNode binaryNode = new ApronIntBinaryNode(pParam1, pParam2,
        Texpr1BinNode.OP_SUB);
    ApronConstraint constraint = new ApronConstraint(Tcons1.SUPEQ, formulaCreator.getEnvironment(),
        binaryNode);
    return constraint;
  }

  @Override
  protected ApronNode lessThan(ApronNode pParam1, ApronNode pParam2) {
    ApronIntBinaryNode binaryNode = new ApronIntBinaryNode(pParam2, pParam1,
        Texpr1BinNode.OP_SUB);
    ApronConstraint constraint = new ApronConstraint(Tcons1.SUP, formulaCreator.getEnvironment(),
        binaryNode);
    return constraint;
  }

  @Override
  protected ApronNode lessOrEquals(ApronNode pParam1, ApronNode pParam2) {
    ApronIntBinaryNode binaryNode = new ApronIntBinaryNode(pParam2, pParam1,
        Texpr1BinNode.OP_SUB);
    ApronConstraint constraint = new ApronConstraint(Tcons1.SUPEQ, formulaCreator.getEnvironment(),
        binaryNode);
    return constraint;
  }
}
