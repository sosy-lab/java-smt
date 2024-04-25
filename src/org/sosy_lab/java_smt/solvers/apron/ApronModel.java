// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.apron;

import apron.Abstract1;
import apron.ApronException;
import apron.Environment;
import apron.Interval;
import apron.Manager;
import apron.MpqScalar;
import apron.Tcons1;
import apron.Texpr0Node;
import apron.Texpr1BinNode;
import apron.Texpr1Node;
import apron.Texpr1UnNode;
import apron.Texpr1VarNode;
import com.google.common.base.Preconditions;
import com.google.common.base.Splitter;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.math.BigInteger;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronConstraint;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntBinaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntCstNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntVarNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatBinaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatCstNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatUnaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatVarNode;

public class ApronModel extends AbstractModel<ApronNode, ApronFormulaType, Environment> {

  private final ApronFormulaCreator formulaCreator;
  private final ApronTheoremProver prover;
  private final ImmutableList<ApronConstraint> assertedExpressions;
  private final ImmutableList<ValueAssignment> model;
  private final ApronBooleanFormulaManager booleanFormulaManager;

  protected ApronModel(
      ApronTheoremProver pProver,
      ApronFormulaCreator creator,
      Collection<ApronConstraint> pAssertedExpressions) {
    super(pProver, creator);
    this.formulaCreator = creator;
    this.prover = pProver;
    this.assertedExpressions = ImmutableList.copyOf(pAssertedExpressions);
    this.booleanFormulaManager = new ApronBooleanFormulaManager(creator);
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
        builder.add(getAssignment(var));
      }
    }
    return builder.build().asList();
  }

  private ValueAssignment getAssignment(String pVar) {
    try {
      // check if the variable is of type integer
      if (formulaCreator.getFormulaEnvironment().isInt(pVar)) {
        return getIntAssignment(pVar);
      } else {
        return getRatAssignment(pVar);
      }
    } catch (ApronException pApronException) {
      throw new RuntimeException(pApronException);
    }
  }

  private ValueAssignment getIntAssignment(String pVar) throws ApronException {
    ImmutableList.Builder<Object> argumentInterpretationBuilder = ImmutableList.builder();
    ApronNode keyFormula = formulaCreator.getVariables().get(pVar);
    Manager man = this.prover.getAbstract1().getCreationManager();
    // shows the interval for all values the variable can take
    Interval interval = this.prover.getAbstract1().getBound(man, pVar);
    // gives the lower bound of the interval
    BigInteger big;
    MpqScalar upperBound = (MpqScalar) interval.sup;
    MpqScalar lowerBound = (MpqScalar) interval.inf;
    // Test if abstract1-object is Bottom
    if (interval.isBottom()) {
      throw new RuntimeException("There is no model because the assertion stack is UNSAT.");
    }
    // is the upper bound +infinity?
    if (upperBound.isInfty() == 1) {
      // is the lower bound -infinity?
      if (lowerBound.isInfty() == -1) {
        big = BigInteger.ZERO;
      } else {
        big = new BigInteger(interval.inf.toString());
      }
    } else {
      big = new BigInteger(interval.sup.toString());
    }
    // valueFormula refers to the lower bound
    ApronIntCstNode valueFormula = new ApronIntCstNode(big);
    // creates a formula of the form: key - lower bound
    ApronIntBinaryNode binaryNode =
        new ApronIntBinaryNode(keyFormula, valueFormula, Texpr1BinNode.OP_SUB);
    // creates a constraint of the form key - lower bound = 0 (Apron format of key = lower bound)
    Map<ApronNode, Integer> map = new HashMap<>();
    map.put(binaryNode, Tcons1.EQ);
    BooleanFormula formula = new ApronConstraint(formulaCreator.getFormulaEnvironment(), map);
    return new ValueAssignment(
        keyFormula,
        valueFormula,
        formula,
        pVar,
        formulaCreator.convertValue(keyFormula, valueFormula),
        argumentInterpretationBuilder.build());
  }

  private ValueAssignment getRatAssignment(String pVar) throws ApronException {
    ImmutableList.Builder<Object> argumentInterpretationBuilder = ImmutableList.builder();
    ApronNode keyFormula = formulaCreator.getVariables().get(pVar);
    Manager man = this.prover.getAbstract1().getCreationManager();
    // shows the interval for all values the variable can take
    Interval interval = this.prover.getAbstract1().getBound(man, pVar);
    // gives the upper bound of the interval
    String strValue;
    MpqScalar upperBound = (MpqScalar) interval.sup;
    MpqScalar lowerBound = (MpqScalar) interval.inf;
    // is the upper bound +infinity?
    if (upperBound.isInfty() == 1) {
      // is the lower bound -infinity?
      if (lowerBound.isInfty() == -1) {
        strValue = "0";
      } else {
        strValue = lowerBound.toString();
      }
    } else {
      strValue = upperBound.toString();
    }
    // translates the value into nominator and denominator
    List<String> numbers = Splitter.on('/').splitToList(strValue);
    BigInteger nominator = new BigInteger(numbers.get(0));
    ApronRatCstNode valueFormula;
    if (numbers.size() > 1) {
      BigInteger denominator = new BigInteger(numbers.get(1));
      valueFormula = new ApronRatCstNode(nominator, denominator);
    } else { // if the value is an integer
      valueFormula = new ApronRatCstNode(nominator, BigInteger.ONE);
    }
    // creates a formula of the form: key - lower bound
    ApronRatBinaryNode binaryNode =
        new ApronRatBinaryNode(keyFormula, valueFormula, Texpr1BinNode.OP_SUB);
    // creates a constraint of the form key - lower bound = 0 (Apron format of key = lower bound)
    Map<ApronNode, Integer> map = new HashMap<>();
    map.put(binaryNode, Tcons1.EQ);
    BooleanFormula formula = new ApronConstraint(formulaCreator.getFormulaEnvironment(), map);
    Object node = formulaCreator.convertValue(keyFormula, valueFormula);
    return new ValueAssignment(
        keyFormula, valueFormula, formula, pVar, node, argumentInterpretationBuilder.build());
  }

  @Override
  protected @Nullable ApronNode evalImpl(ApronNode formula) {
    Preconditions.checkState(!isClosed());
    return getValue(formula);
  }

  /**
   * method for extracting the model value for a variable or more complex formula.
   *
   * @param pNode formula to get a model for
   * @return model value
   */
  public ApronNode getValue(ApronNode pNode) {
    if (pNode instanceof ApronConstraint) {
      // evaluation of equations
      return booleanFormulaManager.makeBooleanImpl(booleanFormulaManager.isTrue(pNode));
    } else {
      Texpr1Node texpr1Node = pNode.getNode();
      Texpr0Node texpr0Node = texpr1Node.toTexpr0Node(formulaCreator.getFormulaEnvironment());
      if (texpr0Node.getDims().length == 0) {
        // if a node has noc variables, return node
        return pNode;
      } else if (pNode instanceof ApronIntVarNode) {
        return getIntVarValue((ApronIntVarNode) pNode);
      } else if (pNode instanceof ApronRatVarNode) {
        return getRatVarValue((ApronRatVarNode) pNode);
      } else {
        return getComplexValue(pNode);
      }
    }
  }

  private ApronNode getComplexValue(ApronNode pNode) {
    Preconditions.checkState(
        !((pNode instanceof ApronIntCstNode)
            || (pNode instanceof ApronIntVarNode)
            || (pNode instanceof ApronRatCstNode)
            || (pNode instanceof ApronRatVarNode)
            || (pNode instanceof ApronConstraint)));

    Texpr1Node nodeToEvaluate = pNode.getNode();
    String resultName = "result";
    // node for storing the result
    Texpr1VarNode resultVar = new Texpr1VarNode(resultName);
    for (ValueAssignment assignment : model) {
      String modelVar = assignment.getName();
      ApronNode toSub = (ApronNode) assignment.getValueAsFormula();
      Texpr1Node toSubT = toSub.getNode();
      // hasVar() only works for Texpr0Node
      Texpr0Node zeroNode = nodeToEvaluate.toTexpr0Node(formulaCreator.getFormulaEnvironment());
      boolean hasVarZero =
          zeroNode.hasDim(formulaCreator.getFormulaEnvironment().dimOfVar(modelVar));
      // if the node to evaluate has the variable of the current assignment, substitute the
      // variable with the assigned value
      if (hasVarZero) {
        // substitutes every occurence of the variable with the value stored in model
        Texpr1Node param1 = nodeToEvaluate.substitute(modelVar, toSubT);
        nodeToEvaluate = param1;
      }
    }
    // if the node to substitute has no variables anymore, build an equation of the form
    // resultVar = nodeToEvaluate; This is the passed to a helper Abstract1 object; The result
    // of the evaluation is a bound of the interval of possible values for resultVar
    if (nodeToEvaluate.getVars().length == 0) {
      // nodeToEvaluate - resultVar
      Texpr1Node result = new Texpr1BinNode(Texpr1BinNode.OP_SUB, nodeToEvaluate, resultVar);
      // nodeToEvaluate - resultVar = 0 --> resultVar = nodeToEvaluate
      Environment environment = new Environment(new String[] {}, new String[] {resultName});
      Tcons1 equation = new Tcons1(environment, Tcons1.EQ, result);
      Tcons1[] c = new Tcons1[] {equation};
      try {
        Abstract1 abstract1 = new Abstract1(prover.getAbstract1().getCreationManager(), c);
        // getting the lower bound of the interval which refers to all values the variable can
        // take
        Object bound =
            abstract1.getBound(prover.getAbstract1().getCreationManager(), resultName).sup;
        String strValue = bound.toString();
        List<String> numbers = Splitter.on('/').splitToList(strValue);
        BigInteger nominator = new BigInteger(numbers.get(0));
        ApronRatCstNode valueFormula;
        if (numbers.size() > 1) { // for rational lower bounds
          BigInteger denominator = new BigInteger(numbers.get(1));
          valueFormula = new ApronRatCstNode(nominator, denominator);
        } else { // if the value is an integer
          valueFormula = new ApronRatCstNode(nominator, BigInteger.ONE);
        }
        return valueFormula;
      } catch (ApronException e) {
        throw new RuntimeException(e);
      }
    } else {
      // if the nodeToEvaluate has still variables, that can not be substituted, the node is
      // returned
      if (nodeToEvaluate instanceof Texpr1VarNode) {
        return new ApronRatVarNode((Texpr1VarNode) nodeToEvaluate, this.formulaCreator);
      } else if (nodeToEvaluate instanceof Texpr1UnNode) {
        return new ApronRatUnaryNode((Texpr1UnNode) nodeToEvaluate);
      } else {
        return new ApronRatBinaryNode((Texpr1BinNode) nodeToEvaluate);
      }
    }
  }

  private ApronNode getIntVarValue(ApronIntVarNode varNode) {
    ApronIntCstNode nullValue = new ApronIntCstNode(BigInteger.ZERO);
    String varName = varNode.getVarName();
    for (ValueAssignment assignment : model) {
      if (varName.equals(assignment.getName())) {
        return (ApronNode) assignment.getValueAsFormula();
      }
    }
    return nullValue;
  }

  private ApronNode getRatVarValue(ApronRatVarNode varNode) {
    ApronIntCstNode nullValue = new ApronIntCstNode(BigInteger.ZERO);
    String varName = varNode.getVarName();
    for (ValueAssignment assignment : model) {
      if (varName.equals(assignment.getName())) {
        return (ApronNode) assignment.getValueAsFormula();
      }
    }
    return nullValue;
  }
}
