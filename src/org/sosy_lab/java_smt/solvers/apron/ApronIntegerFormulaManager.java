// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.apron;

import apron.Tcons1;
import apron.Texpr0Node;
import apron.Texpr1BinNode;
import apron.Texpr1UnNode;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
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
    extends ApronNumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {

  private final ApronFormulaType integerType = new ApronIntegerType();
  private final ApronFormulaCreator apronFormulaCreator;

  protected ApronIntegerFormulaManager(
      ApronFormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
    this.apronFormulaCreator = pCreator;
  }

  @Override
  protected FormulaType getNumeralType() {
    return FormulaType.INTEGER;
  }

  @Override
  protected ApronNode makeVariableImpl(String i) {
    return this.apronFormulaCreator.makeVariable(integerType, i);
  }

  @Override
  protected ApronNode makeNumberImpl(double pNumber) {
    return new ApronIntCstNode(BigDecimal.valueOf(pNumber).toBigInteger());
  }

  @Override
  protected ApronNode makeNumberImpl(BigDecimal pNumber) {
    return new ApronIntCstNode(pNumber.toBigInteger());
  }

  @Override
  protected ApronNode makeNumberImpl(long i) {
    return new ApronIntCstNode(BigInteger.valueOf(i));
  }

  @Override
  protected ApronNode makeNumberImpl(BigInteger i) {
    return new ApronIntCstNode(i);
  }

  @Override
  protected ApronNode makeNumberImpl(String i) {
    return new ApronIntCstNode(new BigInteger(i));
  }

  @Override
  public BooleanFormula modularCongruence(
      IntegerFormula number1, IntegerFormula number2, BigInteger n) {
    return modularCongruence(number1, number2, n.longValue());
  }

  @Override
  public BooleanFormula modularCongruence(IntegerFormula number1, IntegerFormula number2, long n) {
    // (= x (* n (div x n))); div = x/n; x = number1 - number2 Frage ist, ob num1 mod num2 = n ist
    // Test mit 8 und 3 : 8-3 = 2 * (8-3)/2 --> hier entsteht ein fehler
    if (n > 0) {
      ApronIntCstNode nN = new ApronIntCstNode(BigInteger.valueOf(n));
      ApronIntBinaryNode x =
          new ApronIntBinaryNode(
              ApronFormulaManager.getTerm(number1),
              ApronFormulaManager.getTerm(number2),
              Texpr1BinNode.OP_SUB);
      ApronIntBinaryNode div = new ApronIntBinaryNode(x, nN, Texpr1BinNode.OP_DIV);
      ApronIntBinaryNode mul = new ApronIntBinaryNode(nN, div, Texpr1BinNode.OP_MUL);
      ApronIntBinaryNode left = new ApronIntBinaryNode(x, mul, Texpr1BinNode.OP_SUB);
      Map<ApronNode, Integer> map = new HashMap<>();
      map.put(left, Tcons1.EQ);
      return new ApronNode.ApronConstraint(apronFormulaCreator.getFormulaEnvironment(), map);
    }
    ApronIntCstNode zero = new ApronIntCstNode(BigInteger.ZERO);
    Map<ApronNode, Integer> map = new HashMap<>();
    map.put(zero, Tcons1.EQ); // 0=0 for true
    return new ApronConstraint(apronFormulaCreator.getFormulaEnvironment(), map);
  }

  @Override
  public IntegerFormula modulo(IntegerFormula numerator, IntegerFormula denominator) {
    ApronNode node1 = (ApronNode) numerator;
    ApronNode node2 = (ApronNode) denominator;
    Set<String> vars = apronFormulaCreator.getVariables().keySet();
    // Somehow hasVar() only works for level0 of Apron (example in ApronNativeApiTest)
    Texpr0Node zeroNode = node2.getNode().toTexpr0Node(apronFormulaCreator.getFormulaEnvironment());
    for (String var : vars) {
      if (zeroNode.hasDim(apronFormulaCreator.getFormulaEnvironment().dimOfVar(var))) {
        throw new UnsupportedOperationException("Denominator must not contain variables!");
      }
    }
    return new ApronIntBinaryNode(node1, node2, Texpr1BinNode.OP_MOD);
  }

  @Override
  protected ApronNode negate(ApronNode pParam1) {
    return new ApronIntUnaryNode(pParam1, Texpr1UnNode.OP_NEG);
  }

  @Override
  protected ApronNode add(ApronNode pParam1, ApronNode pParam2) {
    return new ApronIntBinaryNode(pParam1, pParam2, Texpr1BinNode.OP_ADD);
  }

  @Override
  protected ApronNode sumImpl(List<ApronNode> operands) {
    if (!operands.isEmpty()) {
      ApronNode first = operands.remove(0);
      for (ApronNode operand : operands) {
        first = new ApronIntBinaryNode(first, operand, Texpr1BinNode.OP_ADD);
      }
      return first;
    }
    return makeNumberImpl(0);
  }

  @Override
  protected ApronNode subtract(ApronNode pParam1, ApronNode pParam2) {
    return new ApronIntBinaryNode(pParam1, pParam2, Texpr1BinNode.OP_SUB);
  }

  @Override
  protected ApronNode divide(ApronNode pParam1, ApronNode pParam2) {
    return new ApronIntBinaryNode(pParam1, pParam2, Texpr1BinNode.OP_DIV);
  }

  @Override
  protected ApronNode multiply(ApronNode pParam1, ApronNode pParam2) {
    return new ApronIntBinaryNode(pParam1, pParam2, Texpr1BinNode.OP_MUL);
  }

  @Override
  protected ApronNode equal(ApronNode pParam1, ApronNode pParam2) {
    ApronIntBinaryNode binaryNode = new ApronIntBinaryNode(pParam1, pParam2, Texpr1BinNode.OP_SUB);
    Map<ApronNode, Integer> map = new HashMap<>();
    map.put(binaryNode, Tcons1.EQ);
    return new ApronConstraint(apronFormulaCreator.getFormulaEnvironment(), map);
  }

  @Override
  protected ApronNode distinctImpl(List<ApronNode> pNumbers) {
    List<ApronConstraint> constraints = new ArrayList<>();
    for (int i = 0; i < pNumbers.size(); i++) {
      for (int j = 0; j < i; j++) {
        ApronNode apronNode =
            new ApronIntBinaryNode(pNumbers.get(i), pNumbers.get(j), Texpr1BinNode.OP_SUB);
        Map<ApronNode, Integer> map = new HashMap<>();
        map.put(apronNode, Tcons1.DISEQ);
        ApronConstraint constraint =
            new ApronConstraint(apronFormulaCreator.getFormulaEnvironment(), map);
        constraints.add(constraint);
      }
    }
    return new ApronConstraint(constraints, apronFormulaCreator.getFormulaEnvironment());
  }

  @Override
  protected ApronNode greaterThan(ApronNode pParam1, ApronNode pParam2) {
    ApronIntBinaryNode binaryNode = new ApronIntBinaryNode(pParam1, pParam2, Texpr1BinNode.OP_SUB);
    Map<ApronNode, Integer> map = new HashMap<>();
    map.put(binaryNode, Tcons1.SUP);
    return new ApronConstraint(apronFormulaCreator.getFormulaEnvironment(), map);
  }

  @Override
  protected ApronNode greaterOrEquals(ApronNode pParam1, ApronNode pParam2) {
    ApronIntBinaryNode binaryNode = new ApronIntBinaryNode(pParam1, pParam2, Texpr1BinNode.OP_SUB);
    Map<ApronNode, Integer> map = new HashMap<>();
    map.put(binaryNode, Tcons1.SUPEQ);
    return new ApronConstraint(apronFormulaCreator.getFormulaEnvironment(), map);
  }

  @Override
  protected ApronNode lessThan(ApronNode pParam1, ApronNode pParam2) {
    ApronIntBinaryNode binaryNode = new ApronIntBinaryNode(pParam2, pParam1, Texpr1BinNode.OP_SUB);
    Map<ApronNode, Integer> map = new HashMap<>();
    map.put(binaryNode, Tcons1.SUP);
    return new ApronConstraint(apronFormulaCreator.getFormulaEnvironment(), map);
  }

  @Override
  protected ApronNode lessOrEquals(ApronNode pParam1, ApronNode pParam2) {
    ApronIntBinaryNode binaryNode = new ApronIntBinaryNode(pParam2, pParam1, Texpr1BinNode.OP_SUB);
    Map<ApronNode, Integer> map = new HashMap<>();
    map.put(binaryNode, Tcons1.SUPEQ);
    return new ApronConstraint(apronFormulaCreator.getFormulaEnvironment(), map);
  }
}
