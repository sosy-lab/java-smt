/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.stp;

import java.math.BigInteger;
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;

class StpBitvectorFormulaManager
    extends AbstractBitvectorFormulaManager<Expr, Type, Long, Long> {

  protected StpBitvectorFormulaManager(StpFormulaCreator pCreator) {
    super(pCreator);
    // TODO Auto-generated constructor stub
  }

  @Override
  protected Expr makeBitvectorImpl(int pLength, Expr pParam1) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr toIntegerFormulaImpl(Expr pI, boolean pSigned) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr negate(Expr pParam1) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr add(Expr pParam1, Expr pParam2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr subtract(Expr pParam1, Expr pParam2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr divide(Expr pParam1, Expr pParam2, boolean pSigned) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr modulo(Expr pParam1, Expr pParam2, boolean pSigned) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr multiply(Expr pParam1, Expr pParam2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr equal(Expr pParam1, Expr pParam2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr greaterThan(Expr pParam1, Expr pParam2, boolean pSigned) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr greaterOrEquals(Expr pParam1, Expr pParam2, boolean pSigned) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr lessThan(Expr pParam1, Expr pParam2, boolean pSigned) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr lessOrEquals(Expr pParam1, Expr pParam2, boolean pSigned) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr not(Expr pParam1) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr and(Expr pParam1, Expr pParam2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr or(Expr pParam1, Expr pParam2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr xor(Expr pParam1, Expr pParam2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr makeBitvectorImpl(int pLength, BigInteger pI) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr makeVariableImpl(int pLength, String pVar) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr shiftRight(Expr pNumber, Expr pToShift, boolean pSigned) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr shiftLeft(Expr pExtract, Expr pExtract2) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr concat(Expr pNumber, Expr pAppend) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr extract(Expr pNumber, int pMsb, int pLsb, boolean pSigned) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Expr extend(Expr pNumber, int pExtensionBits, boolean pSigned) {
    // TODO Auto-generated method stub
    return null;
  }

}