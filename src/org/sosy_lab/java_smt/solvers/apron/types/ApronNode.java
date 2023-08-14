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
import apron.Tcons1;
import apron.Texpr1BinNode;
import apron.Texpr1CstNode;
import apron.Texpr1Node;
import apron.Texpr1UnNode;
import apron.Texpr1VarNode;
import gmp.Mpq;
import gmp.Mpz;
import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.FormulaType;

public interface ApronNode extends Formula {

  FormulaType getType();
  Texpr1Node getNode();

  class ApronCstNode implements ApronNode {

    private FormulaType type;
    private Texpr1CstNode cstNode;

    public ApronCstNode(FormulaType pType, BigInteger pNumerator, BigInteger pDenominator){
      this.type = pType;
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

  class ApronVarNode implements ApronNode{

    private FormulaType type;
    private Texpr1VarNode varNode;

    public ApronVarNode(FormulaType pType, String pVarName){
      this.type = pType;
      this.varNode = new Texpr1VarNode(pVarName);
    }
    @Override
    public FormulaType getType() {
      return this.type;
    }

    public Texpr1VarNode getNode() {
      return varNode;
    }
  }

  class ApronUnaryNode implements ApronNode{
    private FormulaType type;
    private Texpr1UnNode unaryNode;

    public ApronUnaryNode(FormulaType pType, ApronNode param,int op ){
      this.type = pType;
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

  class ApronBinaryNode implements ApronNode{

    private FormulaType type;
    private Texpr1BinNode binaryNode;

    public ApronBinaryNode(FormulaType pType, ApronNode param1, ApronNode param2, int op){
      this.type = pType;
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

  class ApronConstraint implements ApronNode{

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
  }
}
