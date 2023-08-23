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
import com.google.common.base.Preconditions;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import javax.annotation.Nullable;
import org.sosy_lab.common.rationals.Rational;
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
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntCstNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronIntVarNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatCstNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronNumeralNode.ApronRatVarNode;


public class ApronFormulaCreator extends FormulaCreator<ApronNode, ApronFormulaType, Environment,
    Long> {

  private Environment environment;

  /**
   * @variables is a map that stores all variable-objects with their name as key;
   */
  private Map<String, ApronNode> variables;

  protected ApronFormulaCreator(
      Environment pO,
      ApronBooleanType boolType,
      ApronIntegerType pIntegerType,
      ApronRationalType pRationalType,
      @Nullable Long stringType,
      @Nullable Long regexType) {
    super(pO, boolType, pIntegerType, pRationalType, null, null);
    this.environment = pO;
    this.variables = new HashMap<>();
  }

  @Override
  public Object convertValue(ApronNode pf1) {
    FormulaType type = pf1.getType();
    if(pf1 instanceof ApronIntCstNode){
      ApronIntCstNode cst = (ApronIntCstNode) pf1;
      return cst.getValue();
    } else if (pf1 instanceof ApronRatCstNode) {
      ApronRatCstNode cast = (ApronRatCstNode) pf1;
      Rational rational = Rational.of(cast.getNumerator(),cast.getDenominator());
    }
    return null;
  }

  public Environment getEnvironment() {
    return this.environment;
  }

  public void setEnvironment(Environment pEnvironment) {
    environment = pEnvironment;
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
   * @environment as it holds all variables;
   * @param pApronFormulaType Integer or Rational?
   * @param varName name of the variable
   * @return object of either ApronIntVarNode (Type Integer) or ApronRatVarNode (Type Rational)
   */
  @Override
  public ApronNode makeVariable(ApronFormulaType pApronFormulaType, String varName) {
    Preconditions.checkArgument(!environment.hasVar(varName), "Variablename already exists!");
    Preconditions.checkArgument(
        (pApronFormulaType.getType().equals(FormulaType.INTEGER) || pApronFormulaType.getType()
            .equals(
                FormulaType.RATIONAL)),
        "Only Integer or rational variables allowed!");
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
    if(type.equals(FormulaType.BOOLEAN)){
      return org.sosy_lab.java_smt.api.FormulaType.BooleanType;
    } else if (type.equals(FormulaType.RATIONAL)) {
      return org.sosy_lab.java_smt.api.FormulaType.RationalType;
    } else if (type.equals(FormulaType.INTEGER)) {
      return org.sosy_lab.java_smt.api.FormulaType.IntegerType;
    }
    throw new IllegalArgumentException("Type %type not available!");
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, ApronNode f) {
    return null;
  }

  @Override
  public ApronNode callFunctionImpl(Long declaration, List<ApronNode> args) {
    throw new UnsupportedOperationException();
  }

  @Override
  public Long declareUFImpl(
      String pName,
      ApronFormulaType pReturnType,
      List<ApronFormulaType> pArgTypes) {
    return null;
  }

  @Override
  protected Long getBooleanVarDeclarationImpl(ApronNode pApronFormula) {
    return null;
  }
}
