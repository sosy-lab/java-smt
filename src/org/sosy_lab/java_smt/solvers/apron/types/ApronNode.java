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

package org.sosy_lab.java_smt.solvers.apron.types;

import apron.Coeff;
import apron.Environment;
import apron.MpqScalar;
import apron.Scalar;
import apron.StringVar;
import apron.Tcons1;
import apron.Texpr1BinNode;
import apron.Texpr1CstNode;
import apron.Texpr1Node;
import apron.Texpr1UnNode;
import apron.Texpr1VarNode;
import apron.Var;
import com.google.common.base.Preconditions;
import com.google.common.base.Splitter;
import com.google.errorprone.annotations.Immutable;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.solvers.apron.ApronFormulaCreator;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.FormulaType;

/**
 * This is a wrapper for formulas from the Apron-library. All numeral formulas refer to
 * Apron-library instances of Texpr1Node; All BooleanFormulas refer to Tcons1; The wrapper is needed
 * to implement methods that are needed for the JavaSMT-binding but are not provided by the
 * Apron-library. SupressWarnig has to be used, because the internal Texpr1Node form the Apron
 * library is not immutble. But all instances are final.
 */
@SuppressWarnings("Immutable")
public interface ApronNode extends Formula {

  FormulaType getType();

  Texpr1Node getNode();

  /**
   * this array is needed for getting all variable names; it is not possible to directly extract the
   * name of a variable used in an Texpr1Node; that is the reason why the names are tracked
   * additionally.
   *
   * @return String-array with all variables that are used in the created formulas
   */
  Set<String> getVarNames();

  ApronNode getInstance();

  @Immutable
  interface ApronNumeralNode extends ApronNode, NumeralFormula {
    /** This class wraps all rational constants, defined by numerator and denominator. */
    @Immutable
    class ApronRatCstNode implements RationalFormula, ApronNumeralNode {

      private final FormulaType type = FormulaType.RATIONAL;
      private final Texpr1CstNode cstNode;
      private final BigInteger numerator;
      private final BigInteger denominator;

      private final Rational rational;

      public ApronRatCstNode(BigInteger pNumerator, BigInteger pDenominator) {
        this.cstNode = new Texpr1CstNode(new MpqScalar(pNumerator, pDenominator));
        this.numerator = pNumerator;
        this.denominator = pDenominator;
        this.rational = Rational.of(numerator, denominator);
      }

      public ApronRatCstNode(ApronRatCstNode pNode) {
        this.cstNode = pNode.getNode();
        this.numerator = pNode.getNumerator();
        this.denominator = pNode.getDenominator();
        this.rational = Rational.of(numerator, denominator);
      }

      public ApronRatCstNode(Texpr1CstNode pNode) {
        this.cstNode = pNode;
        Coeff coeff = pNode.getConstant();
        Scalar scalar = coeff.inf();
        String string = scalar.toString();
        final List<String> strings = Splitter.on('/').splitToList(string);
        if (strings.size() == 1) {
          this.numerator = BigInteger.valueOf(Long.parseLong(strings.get(0)));
          this.denominator = BigInteger.ONE;
        } else {
          this.numerator = BigInteger.valueOf(Long.parseLong(strings.get(0)));
          this.denominator = BigInteger.valueOf(Long.parseLong(strings.get(0)));
        }
        this.rational = Rational.of(numerator, denominator);
      }

      public Rational getRational() {
        return rational;
      }

      @Override
      public FormulaType getType() {
        return this.type;
      }

      @Override
      public Texpr1CstNode getNode() {
        return cstNode;
      }

      @Override
      public Set<String> getVarNames() {
        return new HashSet<>();
      }

      public BigInteger getDenominator() {
        return denominator;
      }

      public BigInteger getNumerator() {
        return numerator;
      }

      @Override
      public ApronNode getInstance() {
        return this;
      }

      @Override
      public String toString() {
        return cstNode.toString();
      }

      @Override
      public boolean equals(Object other) {
        if (other == this) {
          return true;
        }
        if (!(other instanceof ApronRatCstNode)) {
          return false;
        }
        return this == ((ApronRatCstNode) other).getInstance();
      }

      @Override
      public int hashCode() {
        return this.cstNode.hashCode();
      }
    }

    /** This class wraps variables for rational values. */
    class ApronRatVarNode implements RationalFormula, ApronNumeralNode {

      private final FormulaType type = FormulaType.RATIONAL;
      private final Texpr1VarNode varNode;
      private final String varName;

      private final ApronFormulaCreator formulaCreator;

      public ApronRatVarNode(String pVarName, ApronFormulaCreator pFormulaCreator) {
        this.varNode = new Texpr1VarNode(pVarName);
        this.formulaCreator = pFormulaCreator;
        this.varName = pVarName;
        addVarToEnv();
      }

      public ApronRatVarNode(ApronRatVarNode pNode) {
        this.varNode = pNode.getNode();
        this.varName = pNode.getVarName();
        this.formulaCreator = pNode.getFormulaCreator();
      }

      public ApronRatVarNode(Texpr1VarNode pNode, ApronFormulaCreator pFormulaCreator) {
        Preconditions.checkState(pFormulaCreator.getFormulaEnvironment().hasVar(pNode.toString()));
        this.varNode = pNode;
        this.formulaCreator = pFormulaCreator;
        this.varName = pNode.toString();
      }

      public String getVarName() {
        return varName;
      }

      public ApronFormulaCreator getFormulaCreator() {
        return formulaCreator;
      }

      @Override
      public String toString() {
        return varNode.toString();
      }

      @Override
      public boolean equals(Object other) {

        if (other == this) {
          return true;
        }
        if (!(other instanceof ApronRatVarNode)) {
          return false;
        }
        return this == ((ApronRatVarNode) other).getInstance();
      }

      @Override
      public int hashCode() {
        return this.varNode.hashCode();
      }

      @Override
      public FormulaType getType() {
        return this.type;
      }

      /**
       * this method is needed to add the variable to the Environment; the Environment from the
       * Apron library holds all variables in two separated arrays, one for Integers and one for
       * Rationals; it is a necessary component of an Abstract1 object.
       */
      private void addVarToEnv() {
        Var[] intVars = formulaCreator.getFormulaEnvironment().getIntVars();
        Var[] realVars = formulaCreator.getFormulaEnvironment().getRealVars();
        Var[] newRealVars = new Var[realVars.length + 1];
        int i = 0;
        for (Var var : realVars) {
          newRealVars[i] = var;
          i++;
        }
        newRealVars[realVars.length] = new StringVar(this.varName);
        formulaCreator.setFormulaEnvironment(new Environment(intVars, newRealVars));
      }

      @Override
      public Texpr1VarNode getNode() {
        return varNode;
      }

      @Override
      public Set<String> getVarNames() {
        Set<String> vars = new HashSet<>();
        vars.add(this.varName);
        return vars;
      }

      @Override
      public ApronNode getInstance() {
        return this;
      }
    }

    /**
     * This class wraps terms with unary arithmetic operators for rational values (ex. -x); it is
     * build by an unary operator and a Node;
     */
    class ApronRatUnaryNode implements RationalFormula, ApronNumeralNode {
      private final Texpr1UnNode unaryNode;
      private final Set<String> varNames;

      public ApronRatUnaryNode(ApronNode param, int op) {
        this.unaryNode = new Texpr1UnNode(op, param.getNode());
        this.varNames = param.getVarNames();
      }

      public ApronRatUnaryNode(ApronRatUnaryNode pNode) {
        this.unaryNode = pNode.getNode();
        this.varNames = pNode.getVarNames();
      }

      public ApronRatUnaryNode(Texpr1UnNode pNode) {
        this.unaryNode = pNode;
        Var[] stringVars = pNode.getVars();
        Set<String> variableNames = new HashSet<>();
        for (Var var : stringVars) {
          variableNames.add(var.toString());
        }
        this.varNames = variableNames;
      }

      @Override
      public String toString() {
        return unaryNode.toString();
      }

      @Override
      public boolean equals(Object other) {
        if (other == this) {
          return true;
        }
        if (!(other instanceof ApronRatUnaryNode)) {
          return false;
        }
        return this == ((ApronRatUnaryNode) other).getInstance();
      }

      @Override
      public int hashCode() {
        return this.unaryNode.hashCode();
      }

      @Override
      public FormulaType getType() {
        return null;
      }

      @Override
      public Texpr1UnNode getNode() {
        return this.unaryNode;
      }

      @Override
      public Set<String> getVarNames() {
        return varNames;
      }

      @Override
      public ApronNode getInstance() {
        return this;
      }
    }

    /**
     * This class wraps terms with binary arithmetic operators for rational values (ex. a+4.5); a
     * binary node is defined by a binary operator and two nodes;
     */
    class ApronRatBinaryNode implements RationalFormula, ApronNumeralNode {

      private final FormulaType type = FormulaType.RATIONAL;
      private final Texpr1BinNode binaryNode;
      private final Set<String> varNames;

      public ApronRatBinaryNode(ApronNode param1, ApronNode param2, int op) {
        this.binaryNode = new Texpr1BinNode(op, param1.getNode(), param2.getNode());
        this.varNames = new HashSet<>();
        // adding the variable names of both parameters to @varNames
        this.varNames.addAll(param1.getVarNames());
        this.varNames.addAll(param2.getVarNames());
      }

      public ApronRatBinaryNode(ApronRatBinaryNode pNode) {
        this.binaryNode = pNode.getNode();
        this.varNames = pNode.getVarNames();
      }

      public ApronRatBinaryNode(Texpr1BinNode pNode) {
        this.binaryNode = pNode;
        Var[] stringVars = pNode.getVars();
        Set<String> variableNames = new HashSet<>();
        for (Var var : stringVars) {
          variableNames.add(var.toString());
        }
        this.varNames = variableNames;
      }

      @Override
      public String toString() {
        return binaryNode.toString();
      }

      @Override
      public boolean equals(Object other) {
        if (other == this) {
          return true;
        }
        if (!(other instanceof ApronRatBinaryNode)) {
          return false;
        }
        return this == ((ApronRatBinaryNode) other).getInstance();
      }

      @Override
      public int hashCode() {
        return this.binaryNode.hashCode();
      }

      @Override
      public FormulaType getType() {
        return this.type;
      }

      @Override
      public Texpr1BinNode getNode() {
        return this.binaryNode;
      }

      @Override
      public Set<String> getVarNames() {
        return varNames;
      }

      @Override
      public ApronNode getInstance() {
        return this;
      }
    }

    /** This class wraps integer constants, defined by their BigInteger value. */
    class ApronIntCstNode implements IntegerFormula, ApronNumeralNode {

      private final FormulaType type = FormulaType.INTEGER;
      private final Texpr1CstNode cstNode;
      private final BigInteger value;

      public ApronIntCstNode(BigInteger pNumerator) {
        this.cstNode = new Texpr1CstNode(new MpqScalar(pNumerator));
        this.value = pNumerator;
      }

      public ApronIntCstNode(ApronIntCstNode pNode) {
        this.cstNode = pNode.getNode();
        this.value = pNode.getValue();
      }

      /**
       * constructor for transforming a rational constant to an integer constant.
       *
       * @param ratNode constant formula to transform
       */
      public ApronIntCstNode(ApronRatCstNode ratNode) {
        this.cstNode =
            new Texpr1CstNode(
                new MpqScalar(
                    BigInteger.valueOf(
                        Double.valueOf(Math.floor(ratNode.getRational().doubleValue()))
                            .longValue())));
        this.value =
            BigInteger.valueOf(
                Double.valueOf(Math.floor(ratNode.getRational().doubleValue())).longValue());
      }

      @Override
      public String toString() {
        return cstNode.toString();
      }

      @Override
      public boolean equals(Object other) {

        if (other == this) {
          return true;
        }
        if (!(other instanceof ApronIntCstNode)) {
          return false;
        }
        return this == ((ApronIntCstNode) other).getInstance();
      }

      @Override
      public int hashCode() {
        return this.cstNode.hashCode();
      }

      @Override
      public FormulaType getType() {
        return this.type;
      }

      @Override
      public Texpr1CstNode getNode() {
        return cstNode;
      }

      @Override
      public Set<String> getVarNames() {
        return new HashSet<>();
      }

      public BigInteger getValue() {
        return value;
      }

      @Override
      public ApronNode getInstance() {
        return this;
      }
    }

    /** This class wraps variables for integer values. */
    class ApronIntVarNode implements IntegerFormula, ApronNumeralNode {

      private final FormulaType type = FormulaType.INTEGER;
      private final Texpr1VarNode varNode;
      private final String varName;
      private final ApronFormulaCreator formulaCreator;

      public ApronIntVarNode(String pVarName, ApronFormulaCreator pFormulaCreator) {
        this.varNode = new Texpr1VarNode(pVarName);
        this.varName = pVarName;
        this.formulaCreator = pFormulaCreator;
        addVarToEnv();
      }

      public ApronIntVarNode(ApronIntVarNode pNode) {
        this.varNode = pNode.getNode();
        this.formulaCreator = pNode.getFormulaCreator();
        this.varName = pNode.getVarName();
      }

      /**
       * constructor for converting a rational variable to an integer variable.
       *
       * @param rationalNode variable formula that should be transformed
       */
      public ApronIntVarNode(ApronRatVarNode rationalNode) {
        this.varNode = new Texpr1VarNode(rationalNode.varName);
        this.varName = rationalNode.varName;
        this.formulaCreator = rationalNode.getFormulaCreator();
        // deleting real variable from environment
        Var[] intVars = formulaCreator.getFormulaEnvironment().getIntVars();
        Var[] realVars = formulaCreator.getFormulaEnvironment().getRealVars();
        List<Var> list = new ArrayList<>(Arrays.asList(realVars));
        Var v = new StringVar(varName);
        list.remove(v);
        Var[] newRealVars = new Var[list.size()];
        newRealVars = list.toArray(newRealVars);
        formulaCreator.setFormulaEnvironment(new Environment(intVars, newRealVars));
        // adding int var to Environment
        addVarToEnv();
      }

      public String getVarName() {
        return varName;
      }

      public ApronFormulaCreator getFormulaCreator() {
        return formulaCreator;
      }

      @Override
      public String toString() {
        return varNode.toString();
      }

      @Override
      public boolean equals(Object other) {

        if (other == this) {
          return true;
        }
        if (!(other instanceof ApronIntVarNode)) {
          return false;
        }
        return this == ((ApronIntVarNode) other).getInstance();
      }

      @Override
      public int hashCode() {
        return this.varNode.hashCode();
      }

      @Override
      public FormulaType getType() {
        return this.type;
      }

      @Override
      public Texpr1VarNode getNode() {
        return varNode;
      }

      /**
       * this method is needed to add the variable to the Environment; the Environment from the
       * Apron library holds all variables in two separated arrays, one for Integers and one for
       * Rationals; it is a necessary component of each Abstract1 object.
       */
      private void addVarToEnv() {
        Var[] intVars = formulaCreator.getFormulaEnvironment().getIntVars();
        Var[] realVars = formulaCreator.getFormulaEnvironment().getRealVars();
        Var[] newIntVars = new Var[intVars.length + 1];
        int i = 0;
        for (Var var : intVars) {
          newIntVars[i] = var;
          i++;
        }
        newIntVars[intVars.length] = new StringVar(this.varName);
        formulaCreator.setFormulaEnvironment(new Environment(newIntVars, realVars));
      }

      @Override
      public Set<String> getVarNames() {
        Set<String> vars = new HashSet<>();
        vars.add(this.varName);
        return vars;
      }

      @Override
      public ApronNode getInstance() {
        return this;
      }
    }

    /**
     * This class wraps terms with unary arithmetic operators for integer values (ex. -x); it is
     * build by an unary operator and a node
     */
    class ApronIntUnaryNode implements IntegerFormula, ApronNumeralNode {
      private final Texpr1UnNode unaryNode;
      private final Set<String> varNames;

      public ApronIntUnaryNode(ApronNode param, int op) {
        this.unaryNode =
            new Texpr1UnNode(op, Texpr1Node.RTYPE_INT, Texpr1Node.RDIR_DOWN, param.getNode());
        this.varNames = param.getVarNames();
      }

      public ApronIntUnaryNode(ApronIntUnaryNode pNode) {
        this.unaryNode = pNode.getNode();
        this.unaryNode.setRoundingType(Texpr1Node.RTYPE_INT);
        this.unaryNode.setRoundingDirection(Texpr1Node.RDIR_DOWN);
        this.varNames = pNode.getVarNames();
      }

      /**
       * constructor for transforming a rational formula to an integer formula.
       *
       * @param rationalNode formula to transform
       */
      public ApronIntUnaryNode(ApronRatUnaryNode rationalNode) {
        this.unaryNode = rationalNode.getNode();
        this.unaryNode.setRoundingType(Texpr1Node.RTYPE_INT);
        this.unaryNode.setRoundingDirection(Texpr1Node.RDIR_DOWN);
        this.varNames = rationalNode.getVarNames();
      }

      @Override
      public String toString() {
        return unaryNode.toString();
      }

      @Override
      public boolean equals(Object other) {

        if (other == this) {
          return true;
        }
        if (!(other instanceof ApronIntUnaryNode)) {
          return false;
        }
        return this == ((ApronIntUnaryNode) other).getInstance();
      }

      @Override
      public int hashCode() {
        return this.unaryNode.hashCode();
      }

      @Override
      public FormulaType getType() {
        return null;
      }

      @Override
      public Texpr1UnNode getNode() {
        return this.unaryNode;
      }

      @Override
      public Set<String> getVarNames() {
        return varNames;
      }

      @Override
      public ApronNode getInstance() {
        return this;
      }
    }

    /**
     * This class wraps terms with binary arithmetic operators for integer values (ex. x+3); it is
     * build with an binary operator and two nodes
     */
    class ApronIntBinaryNode implements IntegerFormula, ApronNumeralNode {

      private final FormulaType type = FormulaType.INTEGER;
      private final Texpr1BinNode binaryNode;
      private final Set<String> varNames;

      public ApronIntBinaryNode(ApronNode param1, ApronNode param2, int op) {
        this.binaryNode =
            new Texpr1BinNode(
                op, Texpr1Node.RTYPE_INT, Texpr1Node.RDIR_DOWN, param1.getNode(), param2.getNode());
        // adding the variablenames of both parameters to @varNames
        this.varNames = new HashSet<>();
        varNames.addAll(param1.getVarNames());
        varNames.addAll(param2.getVarNames());
      }

      public ApronIntBinaryNode(ApronIntBinaryNode pNode) {
        this.binaryNode = pNode.getNode();
        this.binaryNode.setRoundingType(Texpr1Node.RTYPE_INT);
        this.binaryNode.setRoundingDirection(Texpr1Node.RDIR_DOWN);
        this.varNames = pNode.getVarNames();
      }

      /**
       * constructor for transforming a rational binary formula to an integer one.
       *
       * @param rationalNode formula to transform
       */
      public ApronIntBinaryNode(ApronRatBinaryNode rationalNode) {
        this.binaryNode = rationalNode.getNode();
        this.binaryNode.setRoundingType(Texpr1Node.RTYPE_INT);
        this.binaryNode.setRoundingDirection(Texpr1Node.RDIR_DOWN);
        this.varNames = rationalNode.getVarNames();
      }

      @Override
      public String toString() {
        return binaryNode.toString();
      }

      @Override
      public boolean equals(Object other) {

        if (other == this) {
          return true;
        }
        if (!(other instanceof ApronIntBinaryNode)) {
          return false;
        }
        return this == ((ApronIntBinaryNode) other).getInstance();
      }

      @Override
      public int hashCode() {
        return this.binaryNode.hashCode();
      }

      @Override
      public FormulaType getType() {
        return this.type;
      }

      @Override
      public Texpr1BinNode getNode() {
        return this.binaryNode;
      }

      @Override
      public Set<String> getVarNames() {
        return varNames;
      }

      @Override
      public ApronNode getInstance() {
        return this;
      }
    }
  }

  /**
   * This class wraps boolean formulas defined by a node and a boolean operator =,!=, >, >=. All
   * boolean formulas in Apron are syntactically like "Texpr1Node operation 0"; a constraint is
   * defined by a map of Texpr1Nodes and an operation. The reason for the map is, that Apron does
   * not have an extra and-operation. Stacking constraints ia a way to implement this for JavaSMT.
   */
  class ApronConstraint implements BooleanFormula, ApronNode {

    private final Map<Tcons1, Texpr1Node> constraintNodes;
    private final List<ApronNode> apronNodes;
    private final Set<String> varNames;

    /**
     * Constructor for building a constraint form a map of nodes and Tcons1-operations (ex.: [
     * (a+1), Tcons1.EQ] -> (a+1) = 0).
     *
     * @param pEnvironment environment of all existing variables
     * @param pConstraints map of nodes and boolean operators
     */
    public ApronConstraint(Environment pEnvironment, Map<ApronNode, Integer> pConstraints) {
      this.constraintNodes = new HashMap<>();
      this.varNames = new HashSet<>();
      this.apronNodes = new ArrayList<>();
      for (Map.Entry<ApronNode, Integer> entry : pConstraints.entrySet()) {
        ApronNode key = entry.getKey();
        Integer kind = entry.getValue();
        Tcons1 tcons1 = new Tcons1(pEnvironment, kind, key.getNode());
        this.constraintNodes.put(tcons1, key.getNode());
        this.varNames.addAll(key.getVarNames());
        this.apronNodes.add(key);
      }
    }

    public ApronConstraint(ApronConstraint pConstraint) {
      this.constraintNodes = pConstraint.getConstraintNodes();
      this.apronNodes = pConstraint.getApronNodes();
      this.varNames = pConstraint.getVarNames();
    }

    /**
     * Constructor for building a new constraint out of a list of constraints.
     *
     * @param pConstraints list of constraints to build a new constraint
     * @param pEnvironment environment of all existing variables
     */
    public ApronConstraint(List<ApronConstraint> pConstraints, Environment pEnvironment) {
      this.constraintNodes = new HashMap<>();
      this.varNames = new HashSet<>();
      this.apronNodes = new ArrayList<>();
      for (ApronConstraint c : pConstraints) {
        for (Map.Entry<Tcons1, Texpr1Node> entry : c.getConstraintNodes().entrySet()) {
          Tcons1 tcons1 = entry.getKey().extendEnvironmentCopy(pEnvironment);
          constraintNodes.put(tcons1, entry.getValue());
        }
        varNames.addAll(c.getVarNames());
        apronNodes.addAll(c.getApronNodes());
      }
    }

    public List<ApronNode> getApronNodes() {
      return apronNodes;
    }

    @Override
    public String toString() {
      StringBuilder builder = new StringBuilder();
      for (Map.Entry<Tcons1, Texpr1Node> node : this.constraintNodes.entrySet()) {
        builder.append(node.getKey().toString()).append("\n");
      }
      return builder.toString();
    }

    @Override
    public boolean equals(Object other) {

      if (other == this) {
        return true;
      }
      if (!(other instanceof ApronConstraint)) {
        return false;
      }
      return this == ((ApronConstraint) other).getInstance();
    }

    @Override
    public int hashCode() {
      return this.constraintNodes.hashCode();
    }

    @Override
    public FormulaType getType() {
      return FormulaType.BOOLEAN;
    }

    /**
     * As constraints can consist of multiple constraints, it is not logical to return just one
     * constraint.
     *
     * @return the left side of the equation; ex.: 2x + 3 < 0 --> 2x + 3
     */
    @Override
    public Texpr1Node getNode() {
      throw new RuntimeException(
          "For ApronConstraints, pleas use getConstraintNodes() or " + "getApronNodes()" + ".");
    }

    public Map<Tcons1, Texpr1Node> getConstraintNodes() {
      return this.constraintNodes;
    }

    @Override
    public Set<String> getVarNames() {
      return varNames;
    }

    @Override
    public ApronNode getInstance() {
      return this;
    }
  }
}
