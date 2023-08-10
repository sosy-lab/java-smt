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
import apron.Linexpr1;
import apron.Linterm1;
import apron.MpqScalar;
import apron.Scalar;
import apron.Var;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.FormulaType;

/**
 * Wrapper-class for Apron Numerical Types;
 */

public interface ApronFormulas extends Formula {

  enum FormulaCategory {
    VAR,
    COEFF,
    TERM,
    EXPRESSION,
    CONSTRAINT
  }

  FormulaCategory getFormulaType();
  FormulaType getType();

  class ApronVar implements ApronFormulas,Var {

    private FormulaType type;
    private String varName;
    private Var apronVar;

    public ApronVar(String pVarName, FormulaType pType){
      this.type = pType;
      this.varName = pVarName;
    }
    @Override
    public FormulaCategory getFormulaType() {
      return FormulaCategory.VAR;
    }

    public String getVarName() {
      return varName;
    }

    @Override
    public FormulaType getType() {
      return type;
    }

    @Override
    public Var clone() {
      return null;
    }

    @Override
    public int compareTo(Var var) {
      ApronVar apronVar1 = (ApronVar) var;
      if (apronVar1.getVarName().equals(this.varName)){
        return 1;
      }
      return 0;
    }
  }

  class ApronCoeff implements ApronFormulas {

    private Coeff apronCoeff;
    private int value;
    private FormulaType type;

    public ApronCoeff(int pValue, FormulaType pType){
      this.apronCoeff = new MpqScalar(pValue);
      this.type = pType;
      this.value = pValue;
    }
    @Override
    public FormulaCategory getFormulaType() {
      return FormulaCategory.COEFF;
    }

    public int getValue() {
      return value;
    }

    public void setValue(int pValue) {
      value = pValue;
      this.apronCoeff = new MpqScalar(pValue);
    }

    @Override
    public FormulaType getType() {
      return type;
    }

    private Coeff getApronCoeff(){
      return apronCoeff;
    }

    public void negate(){
      this.value = (-1)*value;
      this.apronCoeff = new MpqScalar(value);
    }

  }

  class ApronTerm implements ApronFormulas {
    private Linterm1 linterm1;
    private FormulaType type;

    private ApronVar apronVar;
    private ApronCoeff apronCoeff;

    public ApronTerm(String pVar,ApronCoeff pCoeff, FormulaType pType){
      this.linterm1 = new Linterm1(pVar,new MpqScalar(pCoeff.getValue()));
      this.type = pType;
      this.apronVar = new ApronVar(pVar,pType);
      this.apronCoeff = pCoeff;
    }

    @Override
    public FormulaCategory getFormulaType() {
      return FormulaCategory.TERM;
    }

    @Override
    public FormulaType getType() {
      return type;
    }

    private Linterm1 getApronTerm(){
      return linterm1;
    }

    public ApronVar getApronVar() {
      return apronVar;
    }

    public ApronCoeff getApronCoeff() {
      return apronCoeff;
    }
  }

  class ApronExpr implements ApronFormulas {
    private Linexpr1 linexpr1;
    private FormulaType type;
    private ApronTerm[] apronTerms;

    private int cstValue;

    public ApronExpr(ApronTerm[] pApronTerms,int pCstValue,
                     Environment pEnvironment,
                     FormulaType pType){
      Linterm1[] terms = new Linterm1[pApronTerms.length];
      for(int i =0;i<pApronTerms.length;i++){
        Linterm1 term = new Linterm1(apronTerms[i].getApronVar().getVarName(),
            apronTerms[i].getApronCoeff().getApronCoeff());
      }
      this.linexpr1 = new Linexpr1(pEnvironment,terms,new MpqScalar(pCstValue));
      this.type = pType;
      this.cstValue = pCstValue;
      this.apronTerms = pApronTerms;
    }

    @Override
    public FormulaCategory getFormulaType() {
      return FormulaCategory.EXPRESSION;
    }

    @Override
    public FormulaType getType() {
      return type;
    }

    private Linexpr1 getApronExpression(){
      return this.linexpr1;
    }

    public int getCstValue() {
      return cstValue;
    }

    public void setCstValue(int pCstValue) {
      cstValue = pCstValue;
      this.linexpr1.setCst(new MpqScalar(pCstValue));
    }

    public ApronTerm[] getApronTerms() {
      return apronTerms;
    }
  }

  class ApronCons implements ApronFormulas {
    private FormulaType type = FormulaType.BOOLEAN;
    public ApronCons(){

    }

    @Override
    public FormulaCategory getFormulaType() {
      return FormulaCategory.CONSTRAINT;
    }

    @Override
    public FormulaType getType() {
      return type;
    }
  }
}
