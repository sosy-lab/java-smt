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
import apron.MpfrScalar;
import apron.MpqScalar;
import apron.StringVar;
import apron.Tcons1;
import apron.Texpr1BinNode;
import apron.Texpr1CstNode;
import apron.Texpr1Node;
import apron.Texpr1UnNode;
import apron.Texpr1VarNode;
import apron.Var;
import gmp.Mpq;
import gmp.Mpz;
import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.solvers.apron.ApronFormulaCreator;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.FormulaType;

public interface ApronNode extends Formula {

  FormulaType getType();
  Texpr1Node getNode();

  class ApronRatCstNode implements ApronNode, RationalFormula {

    private final FormulaType type = FormulaType.RATIONAL;
    private final Texpr1CstNode cstNode;

    public ApronRatCstNode(BigInteger pNumerator, BigInteger pDenominator){
      this.cstNode = new Texpr1CstNode(new MpqScalar(pNumerator.divide(pDenominator)));
    }

    @Override
    public FormulaType getType() {
      return this.type;
    }

    public Texpr1CstNode getNode() {
      return cstNode;
    }
  }

  class ApronRatVarNode implements ApronNode, RationalFormula{

    private final FormulaType type = FormulaType.RATIONAL;
    private final Texpr1VarNode varNode;
    private final String varName;

    private ApronFormulaCreator formulaCreator;
    public ApronRatVarNode(String pVarName, ApronFormulaCreator pFormulaCreator){
      this.varNode = new Texpr1VarNode(pVarName);
      this.formulaCreator = pFormulaCreator;
      this.varName = pVarName;
    }
    @Override
    public FormulaType getType() {
      return this.type;
    }
    private void addVarToEnv(){
      Var[] intVars = formulaCreator.getEnvironment().getIntVars();
      Var[] realVars = formulaCreator.getEnvironment().getRealVars();
      Var[] newRealVars = new Var[realVars.length+1];
      int i=0;
      for(Var var : realVars){
        newRealVars[i] = var;
        i++;
      }
      newRealVars[realVars.length] = new StringVar(this.varName);
      formulaCreator.setEnvironment(new Environment(intVars, newRealVars));
    }

    public Texpr1VarNode getNode() {
      return varNode;
    }
  }

  class ApronRatUnaryNode implements ApronNode, RationalFormula {
    private final FormulaType type = FormulaType.RATIONAL;
    private final Texpr1UnNode unaryNode;

    public ApronRatUnaryNode(ApronNode param,int op ){
      this.unaryNode = new Texpr1UnNode(op,param.getNode());
    }
    @Override
    public FormulaType getType() {
      return null;
    }

    public Texpr1UnNode getNode(){
      return this.unaryNode;
    }
  }

  class ApronRatBinaryNode implements ApronNode, RationalFormula{

    private FormulaType type = FormulaType.RATIONAL;
    private Texpr1BinNode binaryNode;

    public ApronRatBinaryNode(ApronNode param1, ApronNode param2, int op){
      this.binaryNode = new Texpr1BinNode(op,param1.getNode(),param2.getNode());
    }
    @Override
    public FormulaType getType() {
      return this.type;
    }

    @Override
    public Texpr1Node getNode() {
      return this.binaryNode;
    }
  }

  class ApronIntCstNode implements ApronNode, IntegerFormula {

    private final FormulaType type = FormulaType.INTEGER;
    private final Texpr1CstNode cstNode;

    public ApronIntCstNode(BigInteger pNumerator){
      this.cstNode = new Texpr1CstNode(new MpqScalar(pNumerator));
    }

    @Override
    public FormulaType getType() {
      return this.type;
    }

    public Texpr1CstNode getNode() {
      return cstNode;
    }
  }

  class ApronIntVarNode implements ApronNode, IntegerFormula{

    private final FormulaType type = FormulaType.INTEGER;
    private final Texpr1VarNode varNode;
    private final String varName;
    private final ApronFormulaCreator formulaCreator;

    public ApronIntVarNode(String pVarName, ApronFormulaCreator pFormulaCreator){
      this.varNode = new Texpr1VarNode(pVarName);
      this.varName =pVarName;
      this.formulaCreator = pFormulaCreator;
    }
    @Override
    public FormulaType getType() {
      return this.type;
    }

    public Texpr1VarNode getNode() {
      return varNode;
    }

    private void addVarToEnv(){
      Var[] intVars = formulaCreator.getEnvironment().getIntVars();
      Var[] realVars = formulaCreator.getEnvironment().getRealVars();
      Var[] newIntVars = new Var[intVars.length+1];
      int i=0;
      for(Var var : intVars){
        newIntVars[i] = var;
        i++;
      }
      newIntVars[realVars.length] = new StringVar(this.varName);
      formulaCreator.setEnvironment(new Environment(newIntVars, realVars));
    }

  }

  class ApronIntUnaryNode implements ApronNode, IntegerFormula {
    private final FormulaType type = FormulaType.INTEGER;
    private final Texpr1UnNode unaryNode;

    public ApronIntUnaryNode(ApronNode param,int op ){
      this.unaryNode = new Texpr1UnNode(op,param.getNode());
    }
    @Override
    public FormulaType getType() {
      return null;
    }

    public Texpr1UnNode getNode(){
      return this.unaryNode;
    }
  }

  class ApronIntBinaryNode implements ApronNode, IntegerFormula{

    private final FormulaType type = FormulaType.INTEGER;
    private final Texpr1BinNode binaryNode;

    public ApronIntBinaryNode(ApronNode param1, ApronNode param2, int op){
      this.binaryNode = new Texpr1BinNode(op,param1.getNode(),param2.getNode());
    }
    @Override
    public FormulaType getType() {
      return this.type;
    }

    @Override
    public Texpr1Node getNode() {
      return this.binaryNode;
    }
  }

  class ApronConstraint implements ApronNode, BooleanFormula {

    private Tcons1 constraintNode;
    private Texpr1Node node;
    private int kind;

    public ApronConstraint(int pKind, Environment pEnvironment, Texpr1Node pNode){
      this.constraintNode = new Tcons1(pEnvironment, pKind, pNode);
      this.node = pNode;
      this.kind = pKind;
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
  }
}
