// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.apron;

import apron.Tcons1;
import apron.Texpr1BinNode;
import apron.Texpr1UnNode;
import com.google.common.base.Preconditions;
import com.google.common.base.Splitter;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronRationalType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.FormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronConstraint;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatBinaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatCstNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatUnaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatVarNode;

public class ApronRationalFormulaManager
    extends ApronNumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {

  private final ApronFormulaCreator apronFormulaCreator;
  private final ApronFormulaType rationalType = new ApronRationalType();

  protected ApronRationalFormulaManager(
      ApronFormulaCreator pFormulaCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pFormulaCreator, pNonLinearArithmetic);
    this.apronFormulaCreator = pFormulaCreator;
  }

  @Override
  protected FormulaType getNumeralType() {
    return FormulaType.RATIONAL;
  }

  @Override
  protected ApronNode makeVariableImpl(String i) {
    return apronFormulaCreator.makeVariable(rationalType, i);
  }

  @Override
  protected ApronNode makeNumberImpl(double pNumber) {
    BigDecimal dec = BigDecimal.valueOf(pNumber);
    Rational rat = Rational.ofBigDecimal(dec);
    return new ApronRatCstNode(rat.getNum(), rat.getDen());
  }

  @Override
  protected ApronNode makeNumberImpl(BigDecimal pNumber) {
    Rational rat = Rational.ofBigDecimal(pNumber);
    return new ApronRatCstNode(rat.getNum(), rat.getDen());
  }

  @Override
  protected ApronNode makeNumberImpl(long i) {
    return new ApronRatCstNode(BigInteger.valueOf(i), BigInteger.ONE);
  }

  @Override
  protected ApronNode makeNumberImpl(BigInteger i) {
    return new ApronRatCstNode(i, BigInteger.ONE);
  }

  @Override
  protected ApronNode makeNumberImpl(String i) {
    Preconditions.checkArgument(
        !(i.contains(".") || i.contains(",")), "Rational number has to be written like 2/5.");
    List<String> numbers = Splitter.on('/').splitToList(i);
    BigInteger num = new BigInteger(numbers.get(0));
    if (numbers.size() > 1) {
      BigInteger den = new BigInteger(numbers.get(1));
      return new ApronRatCstNode(num, den);
    }
    return new ApronRatCstNode(num, BigInteger.ONE);
  }

  @Override
  protected ApronNode negate(ApronNode pParam1) {
    return new ApronRatUnaryNode(pParam1, Texpr1UnNode.OP_NEG);
  }

  @Override
  protected ApronNode add(ApronNode pParam1, ApronNode pParam2) {
    return new ApronRatBinaryNode(pParam1, pParam2, Texpr1BinNode.OP_ADD);
  }

  @Override
  protected ApronNode sumImpl(List<ApronNode> operands) {
    if (!operands.isEmpty()) {
      ApronNode first = operands.remove(0);
      for (ApronNode operand : operands) {
        first = new ApronRatBinaryNode(first, operand, Texpr1BinNode.OP_ADD);
      }
      return first;
    }
    return makeNumberImpl(0);
  }

  @Override
  protected ApronNode subtract(ApronNode pParam1, ApronNode pParam2) {
    return new ApronRatBinaryNode(pParam1, pParam2, Texpr1BinNode.OP_SUB);
  }

  @Override
  protected ApronNode divide(ApronNode pParam1, ApronNode pParam2) {
    return new ApronRatBinaryNode(pParam1, pParam2, Texpr1BinNode.OP_DIV);
  }

  @Override
  protected ApronNode multiply(ApronNode pParam1, ApronNode pParam2) {
    return new ApronRatBinaryNode(pParam1, pParam2, Texpr1BinNode.OP_MUL);
  }

  @Override
  protected ApronNode equal(ApronNode pParam1, ApronNode pParam2) {
    ApronRatBinaryNode binaryNode = new ApronRatBinaryNode(pParam1, pParam2, Texpr1BinNode.OP_SUB);
    Map<ApronNode, Integer> map = new HashMap<>();
    map.put(binaryNode, Tcons1.EQ);
    ApronConstraint constraint =
        new ApronConstraint(apronFormulaCreator.getFormulaEnvironment(), map);
    return constraint;
  }

  @Override
  protected ApronNode distinctImpl(List<ApronNode> pNumbers) {
    List<ApronConstraint> constraints = new ArrayList<>();
    for (int i = 0; i < pNumbers.size(); i++) {
      for (int j = 0; j < i; j++) {
        ApronNode apronNode =
            new ApronRatBinaryNode(pNumbers.get(i), pNumbers.get(j), Texpr1BinNode.OP_SUB);
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
    ApronRatBinaryNode binaryNode = new ApronRatBinaryNode(pParam1, pParam2, Texpr1BinNode.OP_SUB);
    Map<ApronNode, Integer> map = new HashMap<>();
    map.put(binaryNode, Tcons1.SUP);
    return new ApronConstraint(apronFormulaCreator.getFormulaEnvironment(), map);
  }

  @Override
  protected ApronNode greaterOrEquals(ApronNode pParam1, ApronNode pParam2) {
    ApronRatBinaryNode binaryNode = new ApronRatBinaryNode(pParam1, pParam2, Texpr1BinNode.OP_SUB);
    Map<ApronNode, Integer> map = new HashMap<>();
    map.put(binaryNode, Tcons1.SUPEQ);
    return new ApronConstraint(apronFormulaCreator.getFormulaEnvironment(), map);
  }

  @Override
  protected ApronNode lessThan(ApronNode pParam1, ApronNode pParam2) {
    ApronRatBinaryNode binaryNode = new ApronRatBinaryNode(pParam2, pParam1, Texpr1BinNode.OP_SUB);
    Map<ApronNode, Integer> map = new HashMap<>();
    map.put(binaryNode, Tcons1.SUP);
    return new ApronConstraint(apronFormulaCreator.getFormulaEnvironment(), map);
  }

  @Override
  protected ApronNode lessOrEquals(ApronNode pParam1, ApronNode pParam2) {
    ApronRatBinaryNode binaryNode = new ApronRatBinaryNode(pParam2, pParam1, Texpr1BinNode.OP_SUB);
    Map<ApronNode, Integer> map = new HashMap<>();
    map.put(binaryNode, Tcons1.SUPEQ);
    return new ApronConstraint(apronFormulaCreator.getFormulaEnvironment(), map);
  }

  @Override
  protected ApronNode floor(ApronNode pTerm) {
    return toInteger(pTerm);
  }

  /**
   * uses especially for this case designed constructors of all Integer Type ApronNode.
   *
   * @param pNumeralNode rational Node
   * @return integer Node
   */
  private ApronNode toInteger(ApronNode pNumeralNode) {
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
