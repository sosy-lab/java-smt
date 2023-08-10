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
import java.util.List;
import javax.annotation.Nullable;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.FormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulas;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronBooleanType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronIntegerType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronRationalType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulas.ApronVar;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulas.FormulaCategory;

public class ApronFormulaCreator extends FormulaCreator<ApronFormulas, ApronFormulaType,Environment,Long> {

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
    return null;
  }

  @Override
  public ApronFormulaType getArrayType(ApronFormulaType indexType, ApronFormulaType elementType) {
    throw new UnsupportedOperationException("Apron does not support array operations.");
  }

  @Override
  public ApronFormulas makeVariable(ApronFormulaType pApronFormulaType, String varName) {
    Preconditions.checkArgument(!environment.hasVar(varName),"Variablename already exists!");
    Preconditions.checkArgument(
        (pApronFormulaType.getType().equals(FormulaType.INTEGER) || pApronFormulaType.getType().equals(
            FormulaType.RATIONAL)),
        "Only Integer or rational variables allowed1");
      if(pApronFormulaType.getType().equals(FormulaType.INTEGER)){
        String[] intvars = new String[]{varName};
        this.environment.add(intvars,new String[]{});
        return new ApronVar(varName,FormulaType.INTEGER);
      }else {
        String[] realvars = new String[]{varName};
        this.environment.add(new String[]{}, realvars);
        return new ApronVar(varName,FormulaType.RATIONAL);
      }
  }

  @Override
  public org.sosy_lab.java_smt.api.FormulaType<ApronFormulas> getFormulaType(ApronFormulas formula) {
    return null;
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, ApronFormulas f) { //hinten
    // anstellen, Frage kann man eine formel in alle kleinteile zerlegen und dann wieder
    // zusammenbauen?
    return null;
  }

  @Override
  public ApronFormulas callFunctionImpl(Long declaration, List<ApronFormulas> args) {
    // not supported
    return null;
  }

  @Override
  public Long declareUFImpl( //not supported
      String pName,
      ApronFormulaType pReturnType,
      List<ApronFormulaType> pArgTypes) {
    return null;
  }

  @Override
  protected Long getBooleanVarDeclarationImpl(ApronFormulas pApronFormula) { //brauche ich nicht
    return null;
  }
}
