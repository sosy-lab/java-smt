/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2020  Dirk Beyer
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
package org.sosy_lab.java_smt.delegate.statistics;

import static com.google.common.base.Preconditions.checkNotNull;

import java.math.BigInteger;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

class StatisticsBitvectorFormulaManager implements BitvectorFormulaManager {

  private final BitvectorFormulaManager delegate;
  private final SolverStatistics stats;

  StatisticsBitvectorFormulaManager(BitvectorFormulaManager pDelegate, SolverStatistics pStats) {
    delegate = checkNotNull(pDelegate);
    stats = checkNotNull(pStats);
  }

  @Override
  public BitvectorFormula makeBitvector(int pLength, long pI) {
    stats.bvOperations.getAndIncrement();
    return delegate.makeBitvector(pLength, pI);
  }

  @Override
  public BitvectorFormula makeBitvector(int pLength, BigInteger pI) {
    stats.bvOperations.getAndIncrement();
    return delegate.makeBitvector(pLength, pI);
  }

  @Override
  public BitvectorFormula makeBitvector(int pLength, IntegerFormula pI) {
    stats.bvOperations.getAndIncrement();
    return delegate.makeBitvector(pLength, pI);
  }

  @Override
  public IntegerFormula toIntegerFormula(BitvectorFormula pI, boolean pSigned) {
    stats.bvOperations.getAndIncrement();
    return delegate.toIntegerFormula(pI, pSigned);
  }

  @Override
  public BitvectorFormula makeVariable(int pLength, String pVar) {
    stats.bvOperations.getAndIncrement();
    return delegate.makeVariable(pLength, pVar);
  }

  @Override
  public BitvectorFormula makeVariable(BitvectorType pType, String pVar) {
    stats.bvOperations.getAndIncrement();
    return delegate.makeVariable(pType, pVar);
  }

  @Override
  public int getLength(BitvectorFormula pNumber) {
    return delegate.getLength(pNumber);
  }

  @Override
  public BitvectorFormula negate(BitvectorFormula pNumber) {
    stats.bvOperations.getAndIncrement();
    return delegate.negate(pNumber);
  }

  @Override
  public BitvectorFormula add(BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    stats.bvOperations.getAndIncrement();
    return delegate.add(pNumber1, pNumber2);
  }

  @Override
  public BitvectorFormula subtract(BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    stats.bvOperations.getAndIncrement();
    return delegate.subtract(pNumber1, pNumber2);
  }

  @Override
  public BitvectorFormula divide(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, boolean pSigned) {
    stats.bvOperations.getAndIncrement();
    return delegate.divide(pNumber1, pNumber2, pSigned);
  }

  @Override
  public BitvectorFormula modulo(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, boolean pSigned) {
    stats.bvOperations.getAndIncrement();
    return delegate.modulo(pNumber1, pNumber2, pSigned);
  }

  @Override
  public BitvectorFormula multiply(BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    stats.bvOperations.getAndIncrement();
    return delegate.multiply(pNumber1, pNumber2);
  }

  @Override
  public BooleanFormula equal(BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    stats.bvOperations.getAndIncrement();
    return delegate.equal(pNumber1, pNumber2);
  }

  @Override
  public BooleanFormula greaterThan(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, boolean pSigned) {
    stats.bvOperations.getAndIncrement();
    return delegate.greaterThan(pNumber1, pNumber2, pSigned);
  }

  @Override
  public BooleanFormula greaterOrEquals(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, boolean pSigned) {
    stats.bvOperations.getAndIncrement();
    return delegate.greaterOrEquals(pNumber1, pNumber2, pSigned);
  }

  @Override
  public BooleanFormula lessThan(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, boolean pSigned) {
    stats.bvOperations.getAndIncrement();
    return delegate.lessThan(pNumber1, pNumber2, pSigned);
  }

  @Override
  public BooleanFormula lessOrEquals(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, boolean pSigned) {
    stats.bvOperations.getAndIncrement();
    return delegate.lessOrEquals(pNumber1, pNumber2, pSigned);
  }

  @Override
  public BitvectorFormula not(BitvectorFormula pBits) {
    stats.bvOperations.getAndIncrement();
    return delegate.not(pBits);
  }

  @Override
  public BitvectorFormula and(BitvectorFormula pBits1, BitvectorFormula pBits2) {
    stats.bvOperations.getAndIncrement();
    return delegate.and(pBits1, pBits2);
  }

  @Override
  public BitvectorFormula or(BitvectorFormula pBits1, BitvectorFormula pBits2) {
    stats.bvOperations.getAndIncrement();
    return delegate.or(pBits1, pBits2);
  }

  @Override
  public BitvectorFormula xor(BitvectorFormula pBits1, BitvectorFormula pBits2) {
    stats.bvOperations.getAndIncrement();
    return delegate.xor(pBits1, pBits2);
  }

  @Override
  public BitvectorFormula shiftRight(
      BitvectorFormula pNumber, BitvectorFormula pToShift, boolean pSigned) {
    stats.bvOperations.getAndIncrement();
    return delegate.shiftRight(pNumber, pToShift, pSigned);
  }

  @Override
  public BitvectorFormula shiftLeft(BitvectorFormula pNumber, BitvectorFormula pToShift) {
    stats.bvOperations.getAndIncrement();
    return delegate.shiftLeft(pNumber, pToShift);
  }

  @Override
  public BitvectorFormula concat(BitvectorFormula pNumber, BitvectorFormula pAppend) {
    stats.bvOperations.getAndIncrement();
    return delegate.concat(pNumber, pAppend);
  }

  @Override
  public BitvectorFormula extract(BitvectorFormula pNumber, int pMsb, int pLsb, boolean pSigned) {
    stats.bvOperations.getAndIncrement();
    return delegate.extract(pNumber, pMsb, pLsb, pSigned);
  }

  @Override
  public BitvectorFormula extend(BitvectorFormula pNumber, int pExtensionBits, boolean pSigned) {
    stats.bvOperations.getAndIncrement();
    return delegate.extend(pNumber, pExtensionBits, pSigned);
  }
}
