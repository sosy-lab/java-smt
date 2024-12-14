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

import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.basicimpl.GeneratorException;
import org.sosy_lab.java_smt.basicimpl.parserInterpreter.FormulaTypesForChecking;


public class SolverLessBitvectorFormulaManager extends AbstractBitvectorFormulaManager<DummyFormula,
    FormulaTypesForChecking, DummyEnv, DummyFunction> {

  DummyFormula dummyIntegerFormula = new DummyFormula(FormulaTypesForChecking.INTEGER);
  DummyFormula dummyBitvectorFormula = new DummyFormula(32);

  protected SolverLessBitvectorFormulaManager(SolverLessFormulaCreator pSolverLessFormulaCreator,
                                              SolverLessBooleanFormulaManager pSolverLessBooleanFormulaManager)
  {
    super(pSolverLessFormulaCreator, pSolverLessBooleanFormulaManager);
  }

  @Override
  protected DummyFormula makeBitvectorImpl(int length, DummyFormula pParam1) {
    return new DummyFormula(length);
  }

  @Override
  protected DummyFormula toIntegerFormulaImpl(DummyFormula pI, boolean signed) {
    return new DummyFormula(FormulaTypesForChecking.INTEGER);
  }

  @Override
  protected DummyFormula makeBitvectorImpl(int pLength, long pI) {
    return new DummyFormula(pLength);
  }

  @Override
  protected DummyFormula distinctImpl(List<DummyFormula> pBits) {
    return super.distinctImpl(pBits);
  }

  @Override
  protected DummyFormula negate(DummyFormula pParam1) {
    return new DummyFormula(pParam1.getBitvectorLength());
  }

  @Override
  protected DummyFormula add(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(Math.max(pParam1.getBitvectorLength(), pParam2.getBitvectorLength()));
  }

  @Override
  protected DummyFormula subtract(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(Math.max(pParam1.getBitvectorLength(), pParam2.getBitvectorLength()));
  }

  @Override
  protected DummyFormula divide(DummyFormula pParam1, DummyFormula pParam2, boolean signed) {
    return new DummyFormula(Math.max(pParam1.getBitvectorLength(), pParam2.getBitvectorLength()));
  }

  @Override
  protected DummyFormula modulo(DummyFormula pParam1, DummyFormula pParam2, boolean signed) {
    return new DummyFormula(Math.max(pParam1.getBitvectorLength(), pParam2.getBitvectorLength()));
  }

  @Override
  protected DummyFormula multiply(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(Math.max(pParam1.getBitvectorLength(), pParam2.getBitvectorLength()));
  }

  @Override
  protected DummyFormula equal(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula greaterThan(DummyFormula pParam1, DummyFormula pParam2, boolean signed) {
    return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula greaterOrEquals(
      DummyFormula pParam1,
      DummyFormula pParam2,
      boolean signed) {
    return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula lessThan(DummyFormula pParam1, DummyFormula pParam2, boolean signed) {
    return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula lessOrEquals(DummyFormula pParam1, DummyFormula pParam2, boolean signed) {
    return new DummyFormula(FormulaTypesForChecking.BOOLEAN);
  }

  @Override
  protected DummyFormula not(DummyFormula pParam1) {
    return new DummyFormula(pParam1.getBitvectorLength());
  }

  @Override
  protected DummyFormula and(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(Math.max(pParam1.getBitvectorLength(), pParam2.getBitvectorLength()));
  }

  @Override
  protected DummyFormula or(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(Math.max(pParam1.getBitvectorLength(), pParam2.getBitvectorLength())); // Boolean formulas do not have a length.
  }

  @Override
  protected DummyFormula xor(DummyFormula pParam1, DummyFormula pParam2) {
    return new DummyFormula(Math.max(pParam1.getBitvectorLength(), pParam2.getBitvectorLength()));
  }

  @Override
  protected DummyFormula makeBitvectorImpl(int pLength, BigInteger pI) {
    return new DummyFormula(pLength);
  }

  @Override
  protected DummyFormula makeVariableImpl(int pLength, String pVar) {
    DummyFormula result = new DummyFormula(pLength);
    result.setName(pVar);
    return result;
  }

  @Override
  protected DummyFormula shiftRight(DummyFormula pNumber, DummyFormula toShift, boolean signed) {
    return new DummyFormula(pNumber.getBitvectorLength());
  }

  @Override
  protected DummyFormula shiftLeft(DummyFormula pExtract, DummyFormula pExtract2) {
    return new DummyFormula(pExtract.getBitvectorLength());
  }

  @Override
  protected DummyFormula concat(DummyFormula number, DummyFormula pAppend) {
    int newLength = number.getBitvectorLength() + pAppend.getBitvectorLength();
    return new DummyFormula(newLength);
  }

  @Override
  protected DummyFormula extract(DummyFormula pNumber, int pMsb, int pLsb) {
    int newLength = pMsb - pLsb + 1;
    return new DummyFormula(newLength);
  }

  @Override
  protected DummyFormula extend(DummyFormula pNumber, int pExtensionBits, boolean pSigned) {
    return new DummyFormula(pNumber.getBitvectorLength() + pExtensionBits);
  }

  public FormulaType<?> getFormulaType(DummyFormula formula){
    if(formula.getFormulaType()==FormulaTypesForChecking.BITVECTOR){
        return FormulaType.getBitvectorTypeWithSize(formula.getBitvectorLength());
    }
    return formula.getFormulaTypeForCreator();
  }


}

