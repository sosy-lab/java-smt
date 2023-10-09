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

import apron.Abstract1;
import apron.ApronException;
import apron.Environment;
import apron.MpqScalar;
import apron.Tcons1;
import apron.Texpr1CstNode;
import apron.Texpr1Node;
import java.awt.TextComponent;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.checkerframework.checker.units.qual.A;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronConstraint;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntCstNode;
import scala.Int;

/**
 * Apron only supports and-operations by stacking constraints. Boolean type variables do not exist.
 */
public class ApronBooleanFormulaManager extends AbstractBooleanFormulaManager<ApronNode,
    ApronFormulaType, Environment, Long> {

  private final ApronFormulaCreator formulaCreator;

  protected ApronBooleanFormulaManager(ApronFormulaCreator pCreator) {
    super(pCreator);
    this.formulaCreator = pCreator;
  }

  @Override
  protected ApronNode makeVariableImpl(String pVar) {
    throw new UnsupportedOperationException("Apron supports only numeral variables.");
  }

  /**
   * True is symbolized by 1=1, false by 1!=1
   * @param value boolean value to implement
   * @return ApronConstraint of the form 1=1 (true) or 1!=1 (false)
   */
  @Override
  protected ApronNode makeBooleanImpl(boolean value) {
    ApronIntCstNode one = new ApronIntCstNode(BigInteger.ONE);
    Map<ApronNode, Integer> map = new HashMap<>();
    if (value){
      map.put(one, Tcons1.EQ);
    } else{
      map.put(one, Tcons1.DISEQ);
    }
    return new ApronConstraint(formulaCreator.getEnvironment(),map);
  }

  @Override
  protected ApronNode not(ApronNode pParam1) {
    throw new UnsupportedOperationException("Apron does not support not() operations.");
  }

  /**
   * the and() method is implemented by stacking two constraints
   * @param pParam1 ApronConstraint 1
   * @param pParam2 ApronConstraint 2
   * @return new ApronConstraint which combines the two input constraints
   */
  @Override
  protected ApronNode and(ApronNode pParam1, ApronNode pParam2) {
    ApronConstraint cons1 = (ApronConstraint) pParam1;
    ApronConstraint cons2 = (ApronConstraint) pParam2;
    ArrayList<ApronConstraint> constraints = new ArrayList<>();
    constraints.add(cons1);
    constraints.add(cons2);
    return new ApronConstraint(constraints, formulaCreator.getEnvironment());
  }

  @Override
  protected ApronNode or(ApronNode pParam1, ApronNode pParam2) {
    throw new UnsupportedOperationException("Apron does not support or() operations.");
  }

  @Override
  protected ApronNode xor(ApronNode pParam1, ApronNode pParam2) {
    throw new UnsupportedOperationException("Apron does not support xor() operations.");
  }

  @Override
  protected ApronNode equivalence(ApronNode bits1, ApronNode bits2) {
    throw new UnsupportedOperationException("Apron does not support equivalence() operations.");
  }

  /**
   * For checking whether a BooleanFormula is true, Apron needs an Abstract1 object with the
   * formula as input. Then one can check, if the Abstract1 object is bottom (for false).
   * @param bits ApronConstraint to check
   * @return !isBottom()
   */
  @Override
  protected boolean isTrue(ApronNode bits) {
    try {
      ApronConstraint constraint = (ApronConstraint) bits;
      Map<Tcons1, Texpr1Node> map = constraint.getConstraintNodes();
      Tcons1[] tcons1s = map.keySet().toArray(new Tcons1[map.size()]);
      Abstract1 helper = new Abstract1(this.formulaCreator.getManager(), tcons1s);
      boolean isBottom = helper.isBottom(this.formulaCreator.getManager());
      return !isBottom;
    } catch (ApronException pException){
      throw  new RuntimeException(pException);
    }   }

  /**
   * For checking whether a BooleanFormula is false, Apron needs an Abstract1 object with the
   * formula as input. Then one can check, if the Abstract1 object is bottom (for false).
   * @param bits ApronConstraint to check
   * @return isBottom()
   */
  @Override
  protected boolean isFalse(ApronNode bits) {
    try {
      ApronConstraint constraint = (ApronConstraint) bits;
      Map<Tcons1, Texpr1Node> map = constraint.getConstraintNodes();
      Tcons1[] tcons1s = map.keySet().toArray(new Tcons1[map.size()]);
      Abstract1 helper = new Abstract1(this.formulaCreator.getManager(), tcons1s);
      return (helper.isBottom(this.formulaCreator.getManager()));
    } catch (ApronException pException){
      throw  new RuntimeException(pException);
    }  }

  @Override
  protected ApronNode ifThenElse(ApronNode cond, ApronNode f1, ApronNode f2) {
    throw new UnsupportedOperationException("Apron does not support ifThenElse() operations.");
  }
}
