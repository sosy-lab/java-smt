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
import org.sosy_lab.java_smt.basicimpl.AbstractBitvectorFormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class SolverLessBitvectorFormulaManager extends AbstractBitvectorFormulaManager<String,
    String, String, String> {

  protected SolverLessBitvectorFormulaManager(
      FormulaCreator<String, String, String, String> pCreator,
      AbstractBooleanFormulaManager<String, String, String, String> pBmgr) {
    super(pCreator, pBmgr);
  }

  @Override
  protected String makeBitvectorImpl(int length, String pParam1) {
    return "";
  }

  @Override
  protected String toIntegerFormulaImpl(String pI, boolean signed) {
    return "";
  }

  @Override
  protected String negate(String pParam1) {
    return "";
  }

  @Override
  protected String add(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String subtract(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String divide(String pParam1, String pParam2, boolean signed) {
    return "";
  }

  @Override
  protected String modulo(String pParam1, String pParam2, boolean signed) {
    return "";
  }

  @Override
  protected String multiply(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String equal(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String greaterThan(String pParam1, String pParam2, boolean signed) {
    return "";
  }

  @Override
  protected String greaterOrEquals(String pParam1, String pParam2, boolean signed) {
    return "";
  }

  @Override
  protected String lessThan(String pParam1, String pParam2, boolean signed) {
    return "";
  }

  @Override
  protected String lessOrEquals(String pParam1, String pParam2, boolean signed) {
    return "";
  }

  @Override
  protected String not(String pParam1) {
    return "";
  }

  @Override
  protected String and(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String or(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String xor(String pParam1, String pParam2) {
    return "";
  }

  @Override
  protected String makeBitvectorImpl(int pLength, BigInteger pI) {
    return "";
  }

  @Override
  protected String makeVariableImpl(int pLength, String pVar) {
    return "";
  }

  @Override
  protected String shiftRight(String pNumber, String toShift, boolean signed) {
    return "";
  }

  @Override
  protected String shiftLeft(String pExtract, String pExtract2) {
    return "";
  }

  @Override
  protected String concat(String number, String pAppend) {
    return "";
  }

  @Override
  protected String extract(String pNumber, int pMsb, int pLsb) {
    return "";
  }

  @Override
  protected String extend(String pNumber, int pExtensionBits, boolean pSigned) {
    return "";
  }
}
