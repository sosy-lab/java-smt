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

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_bvtype_size;
import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_type_of_term;

import apron.Environment;
import com.google.common.base.Preconditions;
import java.util.List;
import javax.annotation.Nullable;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.FormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronBooleanType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronIntegerType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronRationalType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronIntVarNode;
import org.sosy_lab.java_smt.solvers.apron.types.ApronNode.ApronRatVarNode;

public class ApronFormulaCreator extends FormulaCreator<ApronNode, ApronFormulaType,Environment,
    Long> {

  private Environment environment;
  protected ApronFormulaCreator(
      Environment pO,
      ApronBooleanType boolType,
      ApronIntegerType pIntegerType,
      ApronRationalType pRationalType,
      @Nullable Long stringType,
      @Nullable Long regexType) {
    super(pO, boolType, pIntegerType, pRationalType, null, null);
    this.environment = pO;

  }

  public Environment getEnvironment(){
    return this.environment;
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

  @Override
  public ApronNode makeVariable(ApronFormulaType pApronFormulaType, String varName) {
    Preconditions.checkArgument(!environment.hasVar(varName),"Variablename already exists!");
    Preconditions.checkArgument(
        (pApronFormulaType.getType().equals(FormulaType.INTEGER) || pApronFormulaType.getType().equals(
            FormulaType.RATIONAL)),
        "Only Integer or rational variables allowed!");
      if(pApronFormulaType.getType().equals(FormulaType.INTEGER)){
        String[] intvars = new String[]{varName};
        this.environment.add(intvars,new String[]{});
        return new ApronIntVarNode(varName);
      }else {
        String[] realvars = new String[]{varName};
        this.environment.add(new String[]{}, realvars);
        return new ApronRatVarNode(varName);
      }
  }

  @Override
  public <T extends Formula> org.sosy_lab.java_smt.api.FormulaType<T> getFormulaType(T pFormula) {
    return null;
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, ApronNode f) { //hinten
    // anstellen, Frage kann man eine formel in alle kleinteile zerlegen und dann wieder
    // zusammenbauen?
    return null;
  }

  @Override
  public ApronNode callFunctionImpl(Long declaration, List<ApronNode> args) {
    throw  new UnsupportedOperationException();
  }

  @Override
  public Long declareUFImpl(
      String pName,
      ApronFormulaType pReturnType,
      List<ApronFormulaType> pArgTypes) {
    throw new UnsupportedOperationException("Apron does not support uninterpreted functions.");
  }

  @Override
  protected Long getBooleanVarDeclarationImpl(ApronNode pApronFormula) { //brauche ich nicht
    return null;
  }
}
