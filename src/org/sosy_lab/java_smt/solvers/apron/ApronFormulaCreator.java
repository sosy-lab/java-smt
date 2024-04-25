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
import apron.Manager;
import apron.Tcons1;
import apron.Texpr1Node;
import com.google.common.base.Preconditions;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronBooleanType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronIntegerType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronRationalType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.FormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronConstraint;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntBinaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntCstNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntUnaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntVarNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatBinaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatCstNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatUnaryNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatVarNode;

public class ApronFormulaCreator
    extends FormulaCreator<ApronNode, ApronFormulaType, Environment, Long> {

  /** variables is a map that stores all variable-objects with their name as key. */
  private final Map<String, ApronNode> variables;

  private final Manager manager;
  private Environment formulaEnvironment;

  protected ApronFormulaCreator(
      Manager pManager,
      Environment pO,
      ApronBooleanType boolType,
      ApronIntegerType pIntegerType,
      ApronRationalType pRationalType) {
    super(pO, boolType, pIntegerType, pRationalType, null, null);
    this.formulaEnvironment = pO;
    this.variables = new HashMap<>();
    this.manager = pManager;
  }

  /**
   * Method for extracting the value of a formula.
   *
   * @param exprNode an additional formula where the type can be received from.
   * @param value the formula to be converted.
   * @return for constants (actual value), variables (String names) and constraints (Boolean value)
   */
  @Override
  public Object convertValue(ApronNode exprNode, ApronNode value) {
    FormulaType valueType = value.getType();

    // constants
    if (valueType == FormulaType.INTEGER && value instanceof ApronIntCstNode) {
      return ((ApronIntCstNode) value).getValue();
    } else if (valueType == FormulaType.RATIONAL && value instanceof ApronRatCstNode) {
      BigInteger num = ((ApronRatCstNode) value).getNumerator();
      BigInteger den = ((ApronRatCstNode) value).getDenominator();
      Rational div = Rational.of(num, den);
      // for integer values
      if (den.equals(BigInteger.ONE)) {
        return num;
      }
      return div;
    } else if (value instanceof ApronIntVarNode) {
      // integer variables
      return ((ApronIntVarNode) value).getVarName();
    } else if (value instanceof ApronRatVarNode) {
      // rational variables
      return ((ApronRatVarNode) value).getVarName();
    } else if (value instanceof ApronConstraint) {
      // constraints
      try {
        ApronConstraint constraint = (ApronConstraint) value;
        Map<Tcons1, Texpr1Node> map = constraint.getConstraintNodes();
        Tcons1[] tcons1s = map.keySet().toArray(new Tcons1[map.size()]);
        Abstract1 helper = new Abstract1(this.manager, tcons1s);
        return !helper.isBottom(this.manager);
      } catch (ApronException pException) {
        throw new RuntimeException(pException);
      }
    } else {
      return null;
    }
  }

  public Manager getManager() {
    return manager;
  }

  public Environment getFormulaEnvironment() {
    return this.formulaEnvironment;
  }

  public void setFormulaEnvironment(Environment pFormulaEnvironment) {
    formulaEnvironment = pFormulaEnvironment;
  }

  @Override
  public ApronFormulaType getBitvectorType(int bitwidth) {
    throw new UnsupportedOperationException("Apron does not support bitvector operations.");
  }

  @Override
  public ApronFormulaType getFloatingPointType(FloatingPointType type) {
    throw new UnsupportedOperationException("Apron does not support floating point operations.");
  }

  @Override
  public ApronFormulaType getArrayType(ApronFormulaType indexType, ApronFormulaType elementType) {
    throw new UnsupportedOperationException("Apron does not support array operations.");
  }

  /**
   * For making a Formula (Type ApronNode) for a variable it is important to also update the
   * environment!
   *
   * @param pApronFormulaType Integer or Rational?
   * @param varName name of the variable
   * @return object of either ApronIntVarNode (Type Integer) or ApronRatVarNode (Type Rational)
   */
  @Override
  public ApronNode makeVariable(ApronFormulaType pApronFormulaType, String varName) {
    Preconditions.checkArgument(
        (pApronFormulaType.getType().equals(FormulaType.INTEGER)
            || pApronFormulaType.getType().equals(FormulaType.RATIONAL)),
        "Only Integer or rational variables allowed!");
    if (formulaEnvironment.hasVar(varName)) {
      return variables.get(varName);
    }
    if (pApronFormulaType.getType().equals(FormulaType.INTEGER)) {
      ApronIntVarNode varNode = new ApronIntVarNode(varName, this);
      variables.put(varName, varNode);
      return varNode;
    } else {
      ApronRatVarNode varNode = new ApronRatVarNode(varName, this);
      variables.put(varName, varNode);
      return varNode;
    }
  }

  public Map<String, ApronNode> getVariables() {
    return variables;
  }

  @Override
  public org.sosy_lab.java_smt.api.FormulaType<?> getFormulaType(ApronNode formula) {
    FormulaType type = formula.getType();
    if (type.equals(FormulaType.BOOLEAN)) {
      return org.sosy_lab.java_smt.api.FormulaType.BooleanType;
    } else if (type.equals(FormulaType.RATIONAL)) {
      return org.sosy_lab.java_smt.api.FormulaType.RationalType;
    } else if (type.equals(FormulaType.INTEGER)) {
      return org.sosy_lab.java_smt.api.FormulaType.IntegerType;
    }
    throw new IllegalArgumentException("Type" + type + "not available!");
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, ApronNode f) {
    throw new UnsupportedOperationException("Visit function is not supported by Apron.");
  }

  @Override
  public ApronNode callFunctionImpl(Long declaration, List<ApronNode> args) {
    throw new UnsupportedOperationException("Apron does not support callFunctionImpl().");
  }

  @Override
  public Long declareUFImpl(
      String pName, ApronFormulaType pReturnType, List<ApronFormulaType> pArgTypes) {
    return null;
  }

  @Override
  protected Long getBooleanVarDeclarationImpl(ApronNode pApronFormula) {
    return null;
  }

  /**
   * SuppressWarning of unchecked is used here because the unchecked warning was because of
   * unchecked class cast, but as all formulas are instances of ApronNode and ApronNode inherits
   * from Formula, the Class Cast is correct here.
   *
   * @param pType type of the formula
   * @param pTerm term to encapsulate
   * @param <T> all subclasses of ApronNode, all extend Formula
   * @return more specified ApronNode
   */
  @Override
  @SuppressWarnings("unchecked")
  public <T extends Formula> T encapsulate(
      org.sosy_lab.java_smt.api.FormulaType<T> pType, ApronNode pTerm) {
    if (pType.isBooleanType()) {
      ApronConstraint constraint = (ApronConstraint) pTerm;
      return (T) new ApronNode.ApronConstraint(constraint);
    } else if (pType.isIntegerType()) {
      if (pTerm instanceof ApronIntCstNode) {
        ApronIntCstNode node = (ApronIntCstNode) pTerm;
        return (T) new ApronNode.ApronNumeralNode.ApronIntCstNode(node);
      } else if (pTerm instanceof ApronIntVarNode) {
        ApronIntVarNode node = (ApronIntVarNode) pTerm;
        return (T) new ApronNode.ApronNumeralNode.ApronIntVarNode(node);
      } else if (pTerm instanceof ApronIntUnaryNode) {
        ApronIntUnaryNode node = (ApronIntUnaryNode) pTerm;
        return (T) new ApronNode.ApronNumeralNode.ApronIntUnaryNode(node);
      } else if (pTerm instanceof ApronIntBinaryNode) {
        ApronIntBinaryNode node = (ApronIntBinaryNode) pTerm;
        return (T) new ApronNode.ApronNumeralNode.ApronIntBinaryNode(node);
      } else {
        throw new IllegalArgumentException("Term " + pTerm + " not supported in Apron.");
      }
    } else if (pType.isRationalType()) {
      if (pTerm instanceof ApronRatCstNode) {
        ApronRatCstNode node = (ApronRatCstNode) pTerm;
        return (T) new ApronNode.ApronNumeralNode.ApronRatCstNode(node);
      } else if (pTerm instanceof ApronRatVarNode) {
        ApronRatVarNode node = (ApronRatVarNode) pTerm;
        return (T) new ApronNode.ApronNumeralNode.ApronRatVarNode(node);
      } else if (pTerm instanceof ApronRatUnaryNode) {
        ApronRatUnaryNode node = (ApronRatUnaryNode) pTerm;
        return (T) new ApronNode.ApronNumeralNode.ApronRatUnaryNode(node);
      } else if (pTerm instanceof ApronRatBinaryNode) {
        ApronRatBinaryNode node = (ApronRatBinaryNode) pTerm;
        return (T) new ApronNode.ApronNumeralNode.ApronRatBinaryNode(node);
      } else {
        throw new IllegalArgumentException("Term " + pTerm + " not supported in Apron.");
      }

    } else {
      throw new IllegalArgumentException("Type " + pType + " not supported in Apron.");
    }
  }

  @Override
  public ApronNode extractInfo(Formula pT) {
    return ApronFormulaManager.getTerm(pT);
  }

  @Override
  public BooleanFormula encapsulateBoolean(ApronNode pTerm) {
    ApronConstraint constraint = (ApronConstraint) pTerm;
    return new ApronConstraint(constraint);
  }
}
