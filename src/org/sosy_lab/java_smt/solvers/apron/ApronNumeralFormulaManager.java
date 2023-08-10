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

import apron.Environment;
import java.math.BigInteger;
import java.util.HashSet;
import java.util.List;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.FormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulas;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulas.ApronCoeff;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulas.ApronExpr;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulas.ApronTerm;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulas.ApronVar;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulas.FormulaCategory;

abstract class ApronNumeralFormulaManager <
    ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
    ApronFormulas, ApronFormulaType, Environment, ParamFormulaType, ResultFormulaType, Long> {

  private ApronFormulaCreator formulaCreator;
  protected ApronNumeralFormulaManager(
      FormulaCreator<ApronFormulas, ApronFormulaType, Environment, Long> pCreator,
      NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
    this.formulaCreator = (ApronFormulaCreator) pCreator;
  }


  protected boolean isNumeral(ApronFormulas val){
    FormulaType type = val.getType();
    return !type.equals(FormulaType.BOOLEAN);
  }
  protected abstract FormulaType getNumeralType();
  @Override
  protected ApronFormulas makeNumberImpl(long i) {
   // return new ApronCoeff(new MpqScalar(BigInteger.valueOf(i)), i, FormulaType.INTEGER);
    return null;
  }

  @Override
  protected ApronFormulas makeNumberImpl(BigInteger i) {
    //return new ApronCoeff(new MpqScalar(i),i,FormulaType.INTEGER);
    return null;
  }

  @Override
  protected ApronFormulas makeNumberImpl(String i) {
   // return new ApronCoeff(new MpqScalar(Integer.parseInt(i)), Integer.parseInt(i), FormulaType
    // .INTEGER);
    return null;
  }

  @Override
  protected ApronFormulas negate(ApronFormulas pParam1) {
    FormulaCategory category = pParam1.getFormulaType();
    switch(category){
      case VAR:
        ApronVar var = (ApronVar) pParam1;
        return new ApronTerm(((ApronVar) pParam1).getVarName(),new ApronCoeff(-1,pParam1.getType()),
            pParam1.getType());
      case COEFF:
        ApronCoeff coeff = (ApronCoeff) pParam1;
        coeff.negate();
        return coeff;
      case TERM:
        ApronTerm term = (ApronTerm) pParam1;
        term.getApronCoeff().negate();
        return term;
      case EXPRESSION:
        ApronExpr expr = (ApronExpr) pParam1;
        ApronTerm[] terms = expr.getApronTerms();
        ApronTerm[] negTerms = new ApronTerm[terms.length];
        for(int i=0;i<terms.length;i++){
          ApronTerm t = terms[i];
          t.getApronCoeff().negate();
          negTerms[i] = t;
        }
        int negCst = expr.getCstValue()*(-1);
        return new ApronExpr(negTerms,negCst, formulaCreator.getEnvironment(),
            pParam1.getType());
      default:
        throw new IllegalArgumentException("This formula is not negate-able");
    }
  }

  @Override
  protected ApronFormulas add(ApronFormulas pParam1, ApronFormulas pParam2) {
    FormulaCategory param1cat = pParam1.getFormulaType();
    FormulaCategory param2cat = pParam2.getFormulaType();
    FormulaType formulaType = pParam1.getType(); //TODO
    switch (param1cat){
      case COEFF:
        switch (param2cat){
          case COEFF: addCoeffAndCoeff((ApronCoeff) pParam1, (ApronCoeff) pParam2, formulaType);
          case VAR: addCoeffAndVar((ApronCoeff) pParam1,(ApronVar) pParam2,formulaType);
          case TERM: addCoeffAndTerm((ApronCoeff) pParam1, (ApronTerm) pParam2,formulaType);
          case EXPRESSION: addCoeffAndExpr((ApronCoeff) pParam1, (ApronExpr) pParam2, formulaType);
          default: throw new IllegalArgumentException("Coeff can not be added to the second "
              + "Parameter!");
        }
      case VAR:
        switch (param2cat){
          case COEFF: addCoeffAndVar((ApronCoeff) pParam2, (ApronVar) pParam1,formulaType);
          case VAR: addVarAndVar((ApronVar) pParam1, (ApronVar) pParam2,formulaType);
          case TERM: addVarAndTerm((ApronVar) pParam1, (ApronTerm) pParam2,formulaType);
          case EXPRESSION: addVarAndExpr((ApronVar) pParam1, (ApronExpr) pParam2, formulaType);
          default: throw new IllegalArgumentException("Var can not be added to the second "
              + "Parameter!");
        }
      case TERM:
        switch (param2cat){
          case COEFF: addCoeffAndTerm((ApronCoeff) pParam2, (ApronTerm) pParam1,formulaType);
          case VAR: addVarAndTerm((ApronVar) pParam2, (ApronTerm) pParam1,formulaType);
          case TERM: addTermAndTerm((ApronTerm) pParam1,(ApronTerm) pParam2, formulaType);
          case EXPRESSION: addTermAndExpr((ApronTerm) pParam1, (ApronExpr) pParam2, formulaType);
          default:throw new IllegalArgumentException("Term can not be added to the second "
              + "Parameter!");
        }
      case EXPRESSION:
        switch (param2cat){
          case COEFF: addCoeffAndExpr((ApronCoeff) pParam2, (ApronExpr) pParam1,formulaType);
          case VAR: addVarAndExpr((ApronVar) pParam2, (ApronExpr) pParam1,formulaType);
          case TERM: addTermAndExpr((ApronTerm) pParam2, (ApronExpr) pParam1, formulaType);
          case EXPRESSION: addExprAndExpr((ApronExpr) pParam1, (ApronExpr) pParam2, formulaType);
          default: throw new IllegalArgumentException("Expression can not be added to the second "
              + "Parameter!");
        }
      default: throw new IllegalArgumentException("Parameter 1 can not be added to the second "
          + "Parameter!");
    }
  }

  private ApronExpr addCoeffAndVar(ApronCoeff pApronCoeff, ApronVar pVar, FormulaType pType){
    ApronTerm term = new ApronTerm(pVar.getVarName(),new ApronCoeff(1,pType),pType);
    ApronTerm[] terms = new ApronTerm[]{term};
    return new ApronExpr(terms,pApronCoeff.getValue(),formulaCreator.getEnvironment(),pType);
  }

  private ApronCoeff addCoeffAndCoeff(ApronCoeff coeff1, ApronCoeff coeff2, FormulaType pType){
    int newValue = coeff1.getValue() + coeff2.getValue();
    return new ApronCoeff(newValue,pType);
  }

  private ApronExpr addCoeffAndTerm(ApronCoeff coeff, ApronTerm term, FormulaType pType){
    ApronTerm[] linterm1s = new ApronTerm[]{term};
    return new ApronExpr(linterm1s,coeff.getValue(),
        formulaCreator.getEnvironment(),
        pType);
  }

  private ApronExpr addCoeffAndExpr(ApronCoeff apronCoeff, ApronExpr expr, FormulaType pType){
    int newCoeff = apronCoeff.getValue() + expr.getCstValue();
    return new ApronExpr(expr.getApronTerms(),newCoeff,formulaCreator.getEnvironment(),pType);
  }

  private ApronFormulas addVarAndVar(ApronVar var1, ApronVar var2, FormulaType pType){
    if (var1.getVarName().equals(var2.getVarName())){
      return new ApronTerm(var1.getVarName(),new ApronCoeff(2,pType),pType);
    } else {
      ApronTerm linterm1 = new ApronTerm(var1.getVarName(),new ApronCoeff(1,pType),pType);
      ApronTerm linterm2 = new ApronTerm(var2.getVarName(),new ApronCoeff(1,pType),pType);
      ApronTerm[] linterms = new ApronTerm[]{linterm1,linterm2};
      return new ApronExpr(linterms,0,formulaCreator.getEnvironment(),pType);
    }
  }

  private ApronFormulas addVarAndTerm(ApronVar pVar, ApronTerm pTerm, FormulaType pType){
    if (pVar.getVarName().equals(pTerm.getApronVar().getVarName())){
      int newCoeffValue = pTerm.getApronCoeff().getValue() + 1;
      ApronCoeff newCoeff = new ApronCoeff(newCoeffValue,pType);
      return new ApronTerm(pVar.getVarName(), new ApronCoeff(newCoeffValue,pType),pType);
    } else{
      ApronTerm linterm1 = new ApronTerm(pVar.getVarName(), new ApronCoeff(1,pType),pType);
      ApronTerm[] terms = new ApronTerm[]{linterm1,pTerm};
      return new ApronExpr(terms,0,formulaCreator.getEnvironment(),pType);
    }
  }

  private ApronExpr addVarAndExpr(ApronVar pVar, ApronExpr pExpr, FormulaType pType){
    ApronTerm[] terms = pExpr.getApronTerms();
    ApronTerm[] newTerms = new ApronTerm[terms.length+1];
    int i=0;
    for (ApronTerm term :terms) {
      if(term.getApronVar().getVarName().equals(pVar.getVarName())){
        term = new ApronTerm(pVar.getVarName(),new ApronCoeff(term.getApronCoeff().getValue()+1,pType),
            pType);
        return new ApronExpr(terms,pExpr.getCstValue(),formulaCreator.getEnvironment(),pType);
      }
      newTerms[i] = term;
      i++;
    }
    newTerms[terms.length] = new ApronTerm(pVar.getVarName(),new ApronCoeff(1,pType),pType);
    return new ApronExpr(newTerms,pExpr.getCstValue(),formulaCreator.getEnvironment(),pType);
  }

  private ApronFormulas addTermAndTerm(ApronTerm pTerm1, ApronTerm pTerm2, FormulaType pType){
    if (pTerm1.getApronVar().getVarName().equals(pTerm2.getApronVar().getVarName())){
      ApronCoeff newCoeff = new ApronCoeff(pTerm1.getApronCoeff().getValue()+pTerm2.getApronCoeff()
          .getValue(),pType);
      return new ApronTerm(pTerm1.getApronVar().getVarName(),newCoeff,pType);
    } else {
      ApronTerm[] terms = new ApronTerm[]{pTerm1,pTerm2};
      return new ApronExpr(terms, 0,formulaCreator.getEnvironment(),pType);
    }
  }

  private ApronExpr addTermAndExpr(ApronTerm pTerm, ApronExpr pExpr,FormulaType pType){
    ApronTerm[] exprTerms = pExpr.getApronTerms();
    ApronTerm[] newTerms = new ApronTerm[exprTerms.length+1];
    for(int i=0;i<exprTerms.length;i++){
      if(exprTerms[i].getApronVar().getVarName().equals(pTerm.getApronVar().getVarName())){
        exprTerms[i] = new ApronTerm(pTerm.getApronVar().getVarName(),
            new ApronCoeff(exprTerms[i].getApronCoeff().getValue()+1,pType),pType);
        return new ApronExpr(exprTerms,pExpr.getCstValue(),formulaCreator.getEnvironment(),pType);
      }
      newTerms[i] = exprTerms[i];
    }
    newTerms[exprTerms.length] = pTerm;
    return new ApronExpr(newTerms, pExpr.getCstValue(), formulaCreator.getEnvironment(),pType);
  }

  private ApronExpr addExprAndExpr(ApronExpr pExpr1, ApronExpr pExpr2, FormulaType pType){
    ApronTerm[] terms1 = pExpr1.getApronTerms();
    ApronTerm[] terms2 = pExpr2.getApronTerms();
    HashSet<ApronTerm> newTerms = new HashSet<>();
    for(int i = 0; i<terms1.length;i++){
      for(int j=0; j< terms2.length;j++){
        if(terms1[i].getApronVar().getVarName().equals(terms2[j].getApronVar().getVarName())){
          ApronTerm newTerm = new ApronTerm(terms1[i].getApronVar().getVarName(),
              new ApronCoeff(terms1[i].getApronCoeff().getValue()+terms2[j].getApronCoeff().getValue(),pType),pType);
          newTerms.add(newTerm);
        } else {
          newTerms.add(terms2[j]);
        }
      }
      newTerms.add(terms1[i]);
    }
    ApronTerm[] finalTerms = new ApronTerm[newTerms.size()];
    int i=0;
    for(ApronTerm term : newTerms){
      finalTerms[i] = term;
      i++;
    }
    int finalCst = pExpr1.getCstValue()+ pExpr2.getCstValue();
    return new ApronExpr(finalTerms,finalCst,formulaCreator.getEnvironment(),pType);
  }


  @Override
  protected ApronFormulas sumImpl(List<ApronFormulas> operands){
    return null;
  }
  @Override
  protected ApronFormulas subtract(ApronFormulas pParam1, ApronFormulas pParam2) {
    return null;
  }

  @Override
  protected ApronFormulas divide(ApronFormulas pParam1, ApronFormulas pParam2) {
    return null;
  }

  @Override
  protected ApronFormulas multiply(ApronFormulas pParam1, ApronFormulas pParam2) {
    return null;
  }

  @Override
  protected ApronFormulas equal(ApronFormulas pParam1, ApronFormulas pParam2) {
    return null;
  }

  @Override
  protected ApronFormulas distinctImpl(List pNumbers) {
    return null;
  }

  @Override
  protected ApronFormulas greaterThan(ApronFormulas pParam1, ApronFormulas pParam2) {
    return null;
  }

  @Override
  protected ApronFormulas greaterOrEquals(ApronFormulas pParam1, ApronFormulas pParam2) {
    return null;
  }

  @Override
  protected ApronFormulas lessThan(ApronFormulas pParam1, ApronFormulas pParam2) {
    return null;
  }

  @Override
  protected ApronFormulas lessOrEquals(ApronFormulas pParam1, ApronFormulas pParam2) {
    return null;
  }
}
