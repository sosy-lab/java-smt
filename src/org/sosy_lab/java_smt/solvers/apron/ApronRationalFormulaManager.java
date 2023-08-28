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
import com.google.common.base.Preconditions;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ThreadPoolExecutor.AbortPolicy;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronIntegerType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronRationalType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.FormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronConstraint;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntBinaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntCstNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntUnaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntVarNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatBinaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatCstNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatUnaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatVarNode;
import scala.Int;

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
    BigDecimal dec = BigDecimal.valueOf(pNumber);
    Rational rat = Rational.ofBigDecimal(dec);
    return new ApronRatCstNode(rat.getNum(),rat.getDen());  }

  @Override
  protected ApronNode makeNumberImpl(BigDecimal pNumber) {
    String str = pNumber.toPlainString();
    String[] numbers = str.split("\\.");
    int num = Integer.parseInt(numbers[0]);
    if(numbers.length>1) {
      int den = Integer.parseInt(numbers[1]);
      return new ApronRatCstNode(BigInteger.valueOf(num),BigInteger.valueOf(den));
    }
    return new ApronRatCstNode(BigInteger.valueOf(num),BigInteger.ONE);
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
    Preconditions.checkArgument(!(i.contains(".") || i.contains(",")),
        "Rational number has to be written like 2/5.");
    String[] numbers = i.split("/");
    int num = Integer.parseInt(numbers[0]);
    if(numbers.length>1) {
      int den = Integer.parseInt(numbers[1]);
      return new ApronRatCstNode(BigInteger.valueOf(num),BigInteger.valueOf(den));
    }
    return new ApronRatCstNode(BigInteger.valueOf(num),BigInteger.ONE);
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
    throw new UnsupportedOperationException("Apron does not support distinctImpl()");
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

  @Override
  protected ApronNode floor(ApronNode pTerm) {
    return toInteger(pTerm);
  }

  private ApronNode toInteger(ApronNode pNumeralNode){
  FormulaType pType = pNumeralNode.getType();
  if (pType.equals(FormulaType.RATIONAL)) {
      if (pNumeralNode instanceof ApronRatCstNode) {
        ApronRatCstNode node = (ApronRatCstNode) pNumeralNode;
        return new ApronNode.ApronNumeralNode.ApronIntCstNode(node);
      } else if (pNumeralNode instanceof ApronRatVarNode) {
        ApronRatVarNode node = (ApronRatVarNode) pNumeralNode;
        return new ApronNode.ApronNumeralNode.ApronIntVarNode(node);
      } else if (pNumeralNode instanceof ApronRatUnaryNode) {
        ApronRatUnaryNode node = (ApronRatUnaryNode) pNumeralNode;
        return new ApronNode.ApronNumeralNode.ApronRatUnaryNode(node);
      } else if (pNumeralNode instanceof ApronRatBinaryNode) {
        ApronRatBinaryNode node = (ApronRatBinaryNode) pNumeralNode;
        return new ApronNode.ApronNumeralNode.ApronRatBinaryNode(node);
      }
  }
    throw new IllegalArgumentException("Parameter must be rational ApronNode.");

  }

}
