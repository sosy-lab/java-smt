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

package org.sosy_lab.java_smt.solvers.Solverless;
import java.util.List;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.FormulaTypesForChecking;

public class SolverLessFormulaCreator
    extends FormulaCreator<DummyFormula, FormulaTypesForChecking, DummyEnv, DummyFunction> {

  protected SolverLessFormulaCreator(){
    super(new DummyEnv(), FormulaTypesForChecking.BOOLEAN , FormulaTypesForChecking.INTEGER, FormulaTypesForChecking.RATIONAL,
        FormulaTypesForChecking.STRING,
        FormulaTypesForChecking.REGEX);
  }

  @Override
  public FormulaTypesForChecking getBitvectorType(int bitwidth) {
    return FormulaTypesForChecking.BITVECTOR;
  }

  @Override
  public FormulaTypesForChecking getFloatingPointType(FloatingPointType type) {
    return FormulaTypesForChecking.FLOATING_POINT;
  }

  @Override
  public FormulaTypesForChecking getArrayType(
      FormulaTypesForChecking indexType,
      FormulaTypesForChecking elementType) {
    return FormulaTypesForChecking.ARRAY;
  }

  @Override
  public DummyFormula makeVariable(
      FormulaTypesForChecking pFormulaTypesForChecking,
      String varName) {
    return new DummyFormula("", pFormulaTypesForChecking);
  }

  @Override
  public FormulaType<?> getFormulaType(DummyFormula formula) {
    switch (formula.getFormulaTypesForChecking()) {
      case BITVECTOR:
        return FormulaType.getBitvectorTypeWithSize(0);
      case FLOATING_POINT:
        return FormulaType.getFloatingPointType(8, 24);
      case ARRAY:
        return FormulaType.getArrayType(FormulaType.IntegerType, FormulaType.BooleanType);
      case RATIONAL:
        return FormulaType.RationalType;
      case STRING:
        return FormulaType.StringType;
      case REGEX:
        return FormulaType.RegexType;
      case INTEGER:
        return FormulaType.IntegerType;
      default:
        return FormulaType.BooleanType;
    }
  }

  @Override
  public <R> R visit(FormulaVisitor<R> visitor, Formula formula, DummyFormula f) {
    return null;
  }

  @Override
  public DummyFormula callFunctionImpl(DummyFunction declaration, List<DummyFormula> args) {
    return new DummyFormula("", args.get(0).getFormulaTypesForChecking());
  }

  @Override
  public DummyFunction declareUFImpl(
      String pName,
      FormulaTypesForChecking pReturnType,
      List<FormulaTypesForChecking> pArgTypes) {
    return new DummyFunction();
  }

  @Override
  protected DummyFunction getBooleanVarDeclarationImpl(DummyFormula pDummyFormula) {
    return new DummyFunction();
  }


}
