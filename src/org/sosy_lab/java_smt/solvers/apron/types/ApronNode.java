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

import apron.Environment;
import apron.MpqScalar;
import apron.StringVar;
import apron.Tcons1;
import apron.Texpr1BinNode;
import apron.Texpr1CstNode;
import apron.Texpr1Node;
import apron.Texpr1UnNode;
import apron.Texpr1VarNode;
import apron.Var;
import java.math.BigInteger;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.solvers.apron.ApronFormulaCreator;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.FormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatCstNode;

public interface ApronNode extends Formula {

  FormulaType getType();

  Texpr1Node getNode();

  String[] getVarNames();
  ApronNode getInstance();
  interface ApronNumeralNode extends ApronNode, NumeralFormula{
    class ApronRatCstNode
        implements RationalFormula, ApronNumeralNode {

      private final FormulaType type = FormulaType.RATIONAL;
      private final Texpr1CstNode cstNode;
      private final BigInteger numerator;
      private final BigInteger denominator;

      private final Rational rational;

      public ApronRatCstNode(BigInteger pNumerator, BigInteger pDenominator) {
        this.cstNode = new Texpr1CstNode(new MpqScalar(pNumerator.divide(pDenominator)));
        this.numerator = pNumerator;
        this.denominator = pDenominator;
        this.rational = Rational.of(numerator,denominator);
      }

      public ApronRatCstNode(ApronRatCstNode pNode){
        this.cstNode = pNode.getNode();
        this.numerator = pNode.getNumerator();
        this.denominator = pNode.getDenominator();
        this.rational = Rational.of(numerator,denominator);
      }

      public Rational getRational() {
        return rational;
      }

      @Override
      public FormulaType getType() {
        return this.type;
      }

      public Texpr1CstNode getNode() {
        return cstNode;
      }

      @Override
      public String[] getVarNames() {
        return new String[0];
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

    class ApronRatVarNode implements RationalFormula, ApronNode {

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

      public ApronRatVarNode(ApronRatVarNode pNode){
        this.varNode = pNode.getNode();
        this.varName = pNode.getVarName();
        this.formulaCreator = pNode.getFormulaCreator();
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

      private void addVarToEnv() {
        Var[] intVars = formulaCreator.getEnvironment().getIntVars();
        Var[] realVars = formulaCreator.getEnvironment().getRealVars();
        Var[] newRealVars = new Var[realVars.length + 1];
        int i = 0;
        for (Var var : realVars) {
          newRealVars[i] = var;
          i++;
        }
        newRealVars[realVars.length] = new StringVar(this.varName);
        formulaCreator.setEnvironment(new Environment(intVars, newRealVars));
      }

      public Texpr1VarNode getNode() {
        return varNode;
      }

      @Override
      public String[] getVarNames() {
        return new String[]{varName};
      }
      @Override
      public ApronNode getInstance() {
        return this;
      }
    }

    class ApronRatUnaryNode implements RationalFormula, ApronNode {
      private final FormulaType type = FormulaType.RATIONAL;
      private final Texpr1UnNode unaryNode;
      private final String[] varNames;

      public ApronRatUnaryNode(ApronNode param, int op) {
        this.unaryNode = new Texpr1UnNode(op, param.getNode());
        this.varNames = param.getVarNames();
      }

      public ApronRatUnaryNode(ApronRatUnaryNode pNode){
        this.unaryNode = pNode.getNode();
        this.varNames = pNode.getVarNames();
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
        return this == ((ApronRatUnaryNode) other).getInstance();      }

      @Override
      public int hashCode() {
        return this.unaryNode.hashCode();
      }

      @Override
      public FormulaType getType() {
        return null;
      }

      public Texpr1UnNode getNode() {
        return this.unaryNode;
      }

      @Override
      public String[] getVarNames() {
        return varNames;
      }
      @Override
      public ApronNode getInstance() {
        return this;
      }
    }

    class ApronRatBinaryNode implements RationalFormula, ApronNode {

      private final FormulaType type = FormulaType.RATIONAL;
      private final Texpr1BinNode binaryNode;
      private final String[] varNames;

      public ApronRatBinaryNode(ApronNode param1, ApronNode param2, int op) {
        this.binaryNode = new Texpr1BinNode(op, param1.getNode(), param2.getNode());
        String[] varNames1 = param1.getVarNames();
        String[] varNames2 = param2.getVarNames();
        String[] allVarNames = new String[varNames1.length + varNames2.length];
        System.arraycopy(varNames1, 0, allVarNames, 0, varNames1.length);
        int j = varNames1.length - 1;
        for (int i = 0; i < varNames2.length; i++) {
          allVarNames[j] = varNames1[i];
          j++;
        }
        this.varNames = allVarNames;
      }

      public ApronRatBinaryNode(ApronRatBinaryNode pNode){
        this.binaryNode = pNode.getNode();
        this.varNames = pNode.getVarNames();
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
        return this == ((ApronRatBinaryNode) other).getInstance();      }

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
      public String[] getVarNames() {
        return varNames;
      }
      @Override
      public ApronNode getInstance() {
        return this;
      }
    }

    class ApronIntCstNode implements IntegerFormula, ApronNode {

      private final FormulaType type = FormulaType.INTEGER;
      private final Texpr1CstNode cstNode;
      private final BigInteger value;

      public ApronIntCstNode(BigInteger pNumerator) {
        this.cstNode = new Texpr1CstNode(new MpqScalar(pNumerator));
        this.value = pNumerator;
      }

      public ApronIntCstNode(ApronIntCstNode pNode){
        this.cstNode = pNode.getNode();
        this.value = pNode.getValue();
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
        return this == ((ApronIntCstNode) other).getInstance();      }

      @Override
      public int hashCode() {
        return this.cstNode.hashCode();
      }

      @Override
      public FormulaType getType() {
        return this.type;
      }

      public Texpr1CstNode getNode() {
        return cstNode;
      }

      @Override
      public String[] getVarNames() {
        return new String[0];
      }

      public BigInteger getValue() {
        return value;
      }
      @Override
      public ApronNode getInstance() {
        return this;
      }
    }

    class ApronIntVarNode implements IntegerFormula, ApronNode {

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

      public ApronIntVarNode(ApronIntVarNode pNode){
        this.varNode = pNode.getNode();
        this.formulaCreator = pNode.getFormulaCreator();
        this.varName = pNode.getVarName();
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
        return this == ((ApronIntVarNode) other).getInstance();      }

      @Override
      public int hashCode() {
        return this.varNode.hashCode();
      }

      @Override
      public FormulaType getType() {
        return this.type;
      }

      public Texpr1VarNode getNode() {
        return varNode;
      }

      private void addVarToEnv() {
        Var[] intVars = formulaCreator.getEnvironment().getIntVars();
        Var[] realVars = formulaCreator.getEnvironment().getRealVars();
        Var[] newIntVars = new Var[intVars.length + 1];
        int i = 0;
        for (Var var : intVars) {
          newIntVars[i] = var;
          i++;
        }
        newIntVars[intVars.length] = new StringVar(this.varName);
        formulaCreator.setEnvironment(new Environment(newIntVars, realVars));
      }

      @Override
      public String[] getVarNames() {
        return new String[]{varName};
      }
      @Override
      public ApronNode getInstance() {
        return this;
      }
    }

    class ApronIntUnaryNode implements IntegerFormula, ApronNode {
      private final FormulaType type = FormulaType.INTEGER;
      private final Texpr1UnNode unaryNode;
      private final String[] varNames;

      public ApronIntUnaryNode(ApronNode param, int op) {
        this.unaryNode = new Texpr1UnNode(op, param.getNode());
        this.varNames = param.getVarNames();
      }

      public ApronIntUnaryNode(ApronIntUnaryNode pNode){
        this.unaryNode = pNode.getNode();
        this.varNames = pNode.getVarNames();
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
        return this == ((ApronIntUnaryNode) other).getInstance();      }

      @Override
      public int hashCode() {
        return this.unaryNode.hashCode();
      }

      @Override
      public FormulaType getType() {
        return null;
      }

      public Texpr1UnNode getNode() {
        return this.unaryNode;
      }

      @Override
      public String[] getVarNames() {
        return varNames;
      }
      @Override
      public ApronNode getInstance() {
        return this;
      }
    }

    class ApronIntBinaryNode implements IntegerFormula, ApronNode {

      private final FormulaType type = FormulaType.INTEGER;
      private final Texpr1BinNode binaryNode;
      private final String[] varNames;

      public ApronIntBinaryNode(ApronNode param1, ApronNode param2, int op) {
        this.binaryNode = new Texpr1BinNode(op, param1.getNode(), param2.getNode());
        String[] varNames1 = param1.getVarNames();
        String[] varNames2 = param2.getVarNames();
        String[] allVarNames = new String[varNames1.length + varNames2.length];
        System.arraycopy(varNames1, 0, allVarNames, 0, varNames1.length);
        int j = varNames1.length - 1;
        for (int i = 0; i < varNames2.length; i++) {
          allVarNames[j] = varNames1[i];
          j++;
        }
        this.varNames = allVarNames;
      }

      public ApronIntBinaryNode(ApronIntBinaryNode pNode){
        this.binaryNode = pNode.getNode();
        this.varNames = pNode.getVarNames();
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
        return this == ((ApronIntBinaryNode) other).getInstance();      }

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
      public String[] getVarNames() {
        return varNames;
      }
      @Override
      public ApronNode getInstance() {
        return this;
      }
    }
  }


  class ApronConstraint implements BooleanFormula, ApronNode {

    private final Tcons1 constraintNode;
    private final Texpr1Node node;

    private final ApronNode apronNode;
    private final String[] varNames;

    private boolean isTrue;

    public ApronConstraint(int pKind, Environment pEnvironment, ApronNode pNode) {
      this.constraintNode = new Tcons1(pEnvironment, pKind, pNode.getNode());
      this.node = pNode.getNode();
      this.varNames = pNode.getVarNames();
      this.apronNode = pNode;
    }

    public ApronConstraint(ApronConstraint pConstraint){
      this.constraintNode = pConstraint.getConstraintNode();
      this.node = pConstraint.getNode();
      this.apronNode = pConstraint.getApronNode();
      this.varNames = pConstraint.getVarNames();
      this.isTrue = pConstraint.isTrue();
    }

    public boolean isTrue() {
      return isTrue;
    }

    public void setIsTrue(boolean pTrue) {
      isTrue = pTrue;
    }

    @Override
    public String toString() {
      return constraintNode.toString();
    }

    @Override
    public boolean equals(Object other) {

      if (other == this) {
        return true;
      }
      if (!(other instanceof ApronConstraint)) {
        return false;
      }
      return this == ((ApronConstraint) other).getInstance();    }

    @Override
    public int hashCode() {
      return this.constraintNode.hashCode();
    }

    @Override
    public FormulaType getType() {
      return FormulaType.BOOLEAN;
    }

    @Override
    public Texpr1Node getNode() {
      return this.node;
    }

    public Tcons1 getConstraintNode() {
      return constraintNode;
    }

    @Override
    public String[] getVarNames() {
      return varNames;
    }

    public ApronNode getApronNode() {
      return apronNode;
    }
    @Override
    public ApronNode getInstance() {
      return this;
    }
  }
}
