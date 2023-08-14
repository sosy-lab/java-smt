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

import apron.Environment;
import apron.Tcons1;
import apron.Texpr1BinNode;
import apron.Texpr1Node;
import apron.Texpr1UnNode;
import java.math.BigInteger;
import java.util.HashSet;
import java.util.List;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.FormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronBinaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronConstraint;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronUnaryNode;

abstract class ApronNumeralFormulaManager<
    ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
    ApronNode, ApronFormulaType, Environment, ParamFormulaType, ResultFormulaType, Long> {

  private ApronFormulaCreator formulaCreator;

  protected ApronNumeralFormulaManager(
      FormulaCreator<ApronNode, ApronFormulaType, Environment, Long> pCreator,
      NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
    this.formulaCreator = (ApronFormulaCreator) pCreator;
  }


  protected boolean isNumeral(ApronNode val) {
    FormulaType type = val.getType();
    return !type.equals(FormulaType.BOOLEAN);
  }

  protected abstract FormulaType getNumeralType();

  @Override
  protected ApronNode makeNumberImpl(long i) {
    // return new ApronCoeff(new MpqScalar(BigInteger.valueOf(i)), i, FormulaType.INTEGER);
    return null;
  }

  @Override
  protected ApronNode makeNumberImpl(BigInteger i) {
    //return new ApronCoeff(new MpqScalar(i),i,FormulaType.INTEGER);
    return null;
  }

  @Override
  protected ApronNode makeNumberImpl(String i) {
    // return new ApronCoeff(new MpqScalar(Integer.parseInt(i)), Integer.parseInt(i), FormulaType
    // .INTEGER);
    return null;
  }

  @Override
  protected ApronNode negate(ApronNode pParam1) {
    ApronUnaryNode unaryNode = new ApronUnaryNode(pParam1.getType(),pParam1, Texpr1UnNode.OP_NEG);
    return unaryNode;
  }

  @Override
  protected ApronNode add(ApronNode pParam1, ApronNode pParam2) {
    ApronBinaryNode binaryNode = new ApronBinaryNode(pParam1.getType(),pParam1,pParam2,
        Texpr1BinNode.OP_ADD);
    return binaryNode;
  }

  @Override
  protected ApronNode sumImpl(List<ApronNode> operands) {
    return null;
  }

  @Override
  protected ApronNode subtract(ApronNode pParam1, ApronNode pParam2) {
    ApronBinaryNode binaryNode = new ApronBinaryNode(pParam1.getType(), pParam1,pParam2,
        Texpr1BinNode.OP_SUB);
    return binaryNode;
  }

  @Override
  protected ApronNode divide(ApronNode pParam1, ApronNode pParam2) {
    ApronBinaryNode binaryNode = new ApronBinaryNode(pParam1.getType(), pParam1,pParam2,
        Texpr1BinNode.OP_DIV);
    return binaryNode;
  }

  @Override
  protected ApronNode multiply(ApronNode pParam1, ApronNode pParam2) {
    ApronBinaryNode binaryNode = new ApronBinaryNode(pParam1.getType(), pParam1,pParam2,
        Texpr1BinNode.OP_MUL);
    return binaryNode;
  }

  @Override
  protected ApronNode equal(ApronNode pParam1, ApronNode pParam2) {
    ApronBinaryNode binaryNode = new ApronBinaryNode(pParam1.getType(), pParam1,pParam2,
        Texpr1BinNode.OP_SUB);
    ApronConstraint constraint = new ApronConstraint(Tcons1.EQ,formulaCreator.getEnvironment(),
        binaryNode.getNode());
    return constraint;
  }

  @Override
  protected ApronNode distinctImpl(List pNumbers) {
    return null;
  }

  @Override
  protected ApronNode greaterThan(ApronNode pParam1, ApronNode pParam2) {
    ApronBinaryNode binaryNode = new ApronBinaryNode(pParam1.getType(), pParam1,pParam2,
        Texpr1BinNode.OP_SUB);
    ApronConstraint constraint = new ApronConstraint(Tcons1.SUP,formulaCreator.getEnvironment(),
        binaryNode.getNode());
    return constraint;
  }

  @Override
  protected ApronNode greaterOrEquals(ApronNode pParam1, ApronNode pParam2) {
    ApronBinaryNode binaryNode = new ApronBinaryNode(pParam1.getType(), pParam1,pParam2,
        Texpr1BinNode.OP_SUB);
    ApronConstraint constraint = new ApronConstraint(Tcons1.SUPEQ,formulaCreator.getEnvironment(),
        binaryNode.getNode());
    return constraint;
  }

  @Override
  protected ApronNode lessThan(ApronNode pParam1, ApronNode pParam2) {
    ApronBinaryNode binaryNode = new ApronBinaryNode(pParam1.getType(), pParam2,pParam1,
        Texpr1BinNode.OP_SUB);
    ApronConstraint constraint = new ApronConstraint(Tcons1.SUP,formulaCreator.getEnvironment(),
        binaryNode.getNode());
    return constraint;
  }

  @Override
  protected ApronNode lessOrEquals(ApronNode pParam1, ApronNode pParam2) {
    ApronBinaryNode binaryNode = new ApronBinaryNode(pParam1.getType(), pParam2,pParam1,
        Texpr1BinNode.OP_SUB);
    ApronConstraint constraint = new ApronConstraint(Tcons1.SUPEQ,formulaCreator.getEnvironment(),
        binaryNode.getNode());
    return constraint;
  }
}
