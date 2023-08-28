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
import apron.Interval;
import apron.Manager;
import apron.MpqScalar;
import apron.Scalar;
import apron.StringVar;
import apron.Tcons1;
import apron.Texpr0Node;
import apron.Texpr1BinNode;
import apron.Texpr1Node;
import apron.Texpr1VarNode;
import apron.Var;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Objects;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.FormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronConstraint;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntBinaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntCstNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntVarNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatBinaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatCstNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatVarNode;

public class ApronModel extends AbstractModel<ApronNode, ApronFormulaType, Environment> {

  private final ApronFormulaCreator formulaCreator;
  private final ApronTheoremProver prover;
  private final ImmutableList<ApronConstraint> assertedExpressions;
  private final ImmutableList<ValueAssignment> model;

  protected ApronModel(
      ApronTheoremProver pProver,
      ApronFormulaCreator creator,
      Collection<ApronConstraint> pAssertedExpressions) {
    super(pProver, creator);
    this.formulaCreator = creator;
    this.prover = pProver;
    this.assertedExpressions = ImmutableList.copyOf(pAssertedExpressions);
    this.model = generateModel();
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    Preconditions.checkState(!isClosed());
    return generateModel();
  }

  private ImmutableList<ValueAssignment> generateModel() {
    ImmutableSet.Builder<ValueAssignment> builder = ImmutableSet.builder();
    for (ApronConstraint constraint : assertedExpressions) {
      for (String var : constraint.getVarNames()) {
        builder.add(getAssignment(constraint, var));
      }
    }
    return builder.build().asList();
  }

  private ValueAssignment getAssignment(ApronConstraint pFormula, String pVar) {
    ImmutableList.Builder<Object> argumentInterpretationBuilder = ImmutableList.builder();
    try {
      ApronConstraint constraint = pFormula;
      String varName = pVar;
      if (formulaCreator.getEnvironment().isInt(pVar)) {
        ApronNode keyFormula = formulaCreator.getVariables().get(varName);
        Manager man = this.prover.getAbstract1().getCreationManager();
        Interval interval = this.prover.getAbstract1().getBound(man, pVar);
        MpqScalar value = (MpqScalar) interval.sup;
        BigInteger big = BigInteger.valueOf(Long.parseLong(value.toString()));
        ApronIntCstNode valueFormula = new ApronIntCstNode(big);
        ApronIntBinaryNode binaryNode = new ApronIntBinaryNode(keyFormula, valueFormula,
            Texpr1BinNode.OP_SUB);
        BooleanFormula formula = new ApronConstraint(Tcons1.EQ, formulaCreator.getEnvironment(),
            binaryNode); //is the representation x=0, if 0 is the model for x
        return new ValueAssignment(keyFormula, valueFormula, formula, pVar, formulaCreator.convertValue(keyFormula,valueFormula),
            argumentInterpretationBuilder.build());
      } else {
        ApronNode keyFormula = formulaCreator.getVariables().get(varName);
        Manager man = this.prover.getAbstract1().getCreationManager();
        Interval interval = this.prover.getAbstract1().getBound(man, pVar);
        Object value = interval.sup;
        //TODO: unfortunatly it is not possible to extract nominator and denominator out of an
        // Scalar; So all models show Integer Values
        String strValue = value.toString();
        String[] numbers = strValue.split("/");
        BigInteger nominator = BigInteger.valueOf(Long.parseLong(numbers[0]));
        ApronRatCstNode valueFormula;
        if(numbers.length >1){
          BigInteger denominator = BigInteger.valueOf(Long.parseLong(numbers[1]));
          valueFormula = new ApronRatCstNode(nominator,denominator);
        } else {
          valueFormula = new ApronRatCstNode(nominator, BigInteger.ONE);
        }
        ApronRatBinaryNode binaryNode = new ApronRatBinaryNode(keyFormula, valueFormula,
            Texpr1BinNode.OP_SUB);
        BooleanFormula formula = new ApronConstraint(Tcons1.EQ, formulaCreator.getEnvironment(),
            binaryNode);
        Object node = formulaCreator.convertValue(keyFormula,valueFormula);
        return new ValueAssignment(keyFormula, valueFormula, formula, pVar,
            node,
            argumentInterpretationBuilder.build());
      }
    } catch (ApronException pApronException) {
      throw new RuntimeException(pApronException);
    }
  }

  @Override
  protected @Nullable ApronNode evalImpl(ApronNode formula) {
    Preconditions.checkState(!isClosed());
    return getValue(formula);
  }

  protected ApronNode getValue(ApronNode pNode) {
    if (pNode instanceof ApronIntVarNode) {
      ApronIntVarNode varNode = (ApronIntVarNode) pNode;
      String varName = varNode.getVarName();
      for (ValueAssignment assignment : model) {
        if (varName.equals(assignment.getName())) {
          return (ApronNode) assignment.getValueAsFormula();
        }
      }
    } else if (pNode instanceof ApronRatVarNode) {
      ApronRatVarNode varNode = (ApronRatVarNode) pNode;
      String varName = varNode.getVarName();
      for (ValueAssignment assignment : model) {
        if (varName.equals(assignment.getName())) {
          return (ApronNode) assignment.getValueAsFormula();
        }
      }
    }
    else {
      Texpr1Node node = pNode.getNode();
      List<String> modelVars = new ArrayList<>();
      for (ValueAssignment assignment:model) {
        String modelVar = assignment.getName();
        StringVar apronVar = new StringVar(modelVar);
        ApronNode toSub = (ApronNode) assignment.getValueAsFormula();
        Texpr1Node toSubT = toSub.getNode();
        //hasVar() only works for Texpr0Node
        Texpr0Node zeroNode = node.toTexpr0Node(prover.getAbstract1().getEnvironment());
        boolean hasVarZero =
            zeroNode.hasDim(prover.getAbstract1().getEnvironment().dimOfVar(modelVar));
        if(hasVarZero){
          try {
            Texpr1Node param1 = node.substitute(modelVar,toSubT); //substitutes every occurence of
            // the variable with the value stored in model
            Texpr1VarNode var = new Texpr1VarNode(modelVar);
            Texpr1Node equation = new Texpr1BinNode(Texpr1BinNode.OP_SUB,param1,var); // param1
            // -variable
            Tcons1 cons = new Tcons1(formulaCreator.getEnvironment(),Tcons1.EQ,equation);
            Tcons1[] c = new Tcons1[]{cons};
            Abstract1 abstract1 = new Abstract1(prover.getAbstract1().getCreationManager(),c);
            Object bound =
                abstract1.getBound(prover.getAbstract1().getCreationManager(), modelVar).sup;
            int value = Integer.parseInt(bound.toString());
            return new ApronIntCstNode(BigInteger.valueOf(value));
          } catch (ApronException e){
            throw new RuntimeException(e);
          }
        }
      }
    }
    return pNode;
  }

/*  @Override
  public @Nullable Rational evaluate(RationalFormula f) {
    if(f instanceof ApronRatCstNode){
      return ((ApronRatCstNode) f).getRational();
    } return null;
  }*/

}
