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
package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager.checkVariableName;

import java.math.BigInteger;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;

public abstract class AbstractBitvectorFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements BitvectorFormulaManager {

  protected AbstractBitvectorFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pCreator) {
    super(pCreator);
  }

  private BitvectorFormula wrap(TFormulaInfo pTerm) {
    return getFormulaCreator().encapsulateBitvector(pTerm);
  }

  private void checkSameSize(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, String operation) {
    final int len1 = getLength(pNumber1);
    final int len2 = getLength(pNumber2);
    checkArgument(
        len1 == len2,
        "Can't %s bitvectors with different sizes (%s and %s)",
        operation,
        len1,
        len2);
  }

  @Override
  public BitvectorFormula negate(BitvectorFormula pNumber) {
    TFormulaInfo param1 = extractInfo(pNumber);
    return wrap(negate(param1));
  }

  protected abstract TFormulaInfo negate(TFormulaInfo pParam1);

  @Override
  public BitvectorFormula add(BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    checkSameSize(pNumber1, pNumber2, "add");
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrap(add(param1, param2));
  }

  protected abstract TFormulaInfo add(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BitvectorFormula subtract(BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    checkSameSize(pNumber1, pNumber2, "subtract");
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrap(subtract(param1, param2));
  }

  protected abstract TFormulaInfo subtract(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BitvectorFormula divide(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, boolean signed) {
    checkSameSize(pNumber1, pNumber2, "divide");
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrap(divide(param1, param2, signed));
  }

  protected abstract TFormulaInfo divide(
      TFormulaInfo pParam1, TFormulaInfo pParam2, boolean signed);

  @Override
  public BitvectorFormula modulo(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, boolean signed) {
    checkSameSize(pNumber1, pNumber2, "modulo");
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrap(modulo(param1, param2, signed));
  }

  protected abstract TFormulaInfo modulo(
      TFormulaInfo pParam1, TFormulaInfo pParam2, boolean signed);

  @Override
  public BitvectorFormula multiply(BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    checkSameSize(pNumber1, pNumber2, "modulo");
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrap(multiply(param1, param2));
  }

  protected abstract TFormulaInfo multiply(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula equal(BitvectorFormula pNumber1, BitvectorFormula pNumber2) {
    checkSameSize(pNumber1, pNumber2, "compare");
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(equal(param1, param2));
  }

  protected abstract TFormulaInfo equal(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BooleanFormula greaterThan(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, boolean signed) {
    checkSameSize(pNumber1, pNumber2, "compare");
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(greaterThan(param1, param2, signed));
  }

  protected abstract TFormulaInfo greaterThan(
      TFormulaInfo pParam1, TFormulaInfo pParam2, boolean signed);

  @Override
  public BooleanFormula greaterOrEquals(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, boolean signed) {
    checkSameSize(pNumber1, pNumber2, "compare");
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(greaterOrEquals(param1, param2, signed));
  }

  protected abstract TFormulaInfo greaterOrEquals(
      TFormulaInfo pParam1, TFormulaInfo pParam2, boolean signed);

  @Override
  public BooleanFormula lessThan(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, boolean signed) {
    checkSameSize(pNumber1, pNumber2, "compare");
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(lessThan(param1, param2, signed));
  }

  protected abstract TFormulaInfo lessThan(
      TFormulaInfo pParam1, TFormulaInfo pParam2, boolean signed);

  @Override
  public BooleanFormula lessOrEquals(
      BitvectorFormula pNumber1, BitvectorFormula pNumber2, boolean signed) {
    checkSameSize(pNumber1, pNumber2, "compare");
    TFormulaInfo param1 = extractInfo(pNumber1);
    TFormulaInfo param2 = extractInfo(pNumber2);

    return wrapBool(lessOrEquals(param1, param2, signed));
  }

  protected abstract TFormulaInfo lessOrEquals(
      TFormulaInfo pParam1, TFormulaInfo pParam2, boolean signed);

  @Override
  public BitvectorFormula not(BitvectorFormula pBits) {
    TFormulaInfo param1 = extractInfo(pBits);
    return wrap(not(param1));
  }

  protected abstract TFormulaInfo not(TFormulaInfo pParam1);

  @Override
  public BitvectorFormula and(BitvectorFormula pBits1, BitvectorFormula pBits2) {
    assert getLength(pBits1) == getLength(pBits2);
    TFormulaInfo param1 = extractInfo(pBits1);
    TFormulaInfo param2 = extractInfo(pBits2);

    return wrap(and(param1, param2));
  }

  protected abstract TFormulaInfo and(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BitvectorFormula or(BitvectorFormula pBits1, BitvectorFormula pBits2) {
    assert getLength(pBits1) == getLength(pBits2);
    TFormulaInfo param1 = extractInfo(pBits1);
    TFormulaInfo param2 = extractInfo(pBits2);

    return wrap(or(param1, param2));
  }

  protected abstract TFormulaInfo or(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BitvectorFormula xor(BitvectorFormula pBits1, BitvectorFormula pBits2) {
    assert getLength(pBits1) == getLength(pBits2);
    TFormulaInfo param1 = extractInfo(pBits1);
    TFormulaInfo param2 = extractInfo(pBits2);

    return wrap(xor(param1, param2));
  }

  protected abstract TFormulaInfo xor(TFormulaInfo pParam1, TFormulaInfo pParam2);

  @Override
  public BitvectorFormula makeBitvector(int pLength, long i) {
    return wrap(makeBitvectorImpl(pLength, i));
  }

  protected abstract TFormulaInfo makeBitvectorImpl(int pLength, long pI);

  @Override
  public BitvectorFormula makeBitvector(int pLength, BigInteger i) {
    return wrap(makeBitvectorImpl(pLength, i));
  }

  protected abstract TFormulaInfo makeBitvectorImpl(int pLength, BigInteger pI);

  @Override
  public BitvectorFormula makeVariable(BitvectorType type, String pVar) {
    return makeVariable(type.getSize(), pVar);
  }

  @Override
  public BitvectorFormula makeVariable(int pLength, String pVar) {
    checkVariableName(pVar);
    return wrap(makeVariableImpl(pLength, pVar));
  }

  protected abstract TFormulaInfo makeVariableImpl(int pLength, String pVar);

  /**
   * Return a term representing the (arithmetic if signed is true) right shift of number by toShift.
   */
  @Override
  public BitvectorFormula shiftRight(
      BitvectorFormula pNumber, BitvectorFormula toShift, boolean signed) {
    TFormulaInfo param1 = extractInfo(pNumber);
    TFormulaInfo param2 = extractInfo(toShift);

    return wrap(shiftRight(param1, param2, signed));
  }

  protected abstract TFormulaInfo shiftRight(
      TFormulaInfo pNumber, TFormulaInfo toShift, boolean signed);

  @Override
  public BitvectorFormula shiftLeft(BitvectorFormula pNumber, BitvectorFormula toShift) {
    TFormulaInfo param1 = extractInfo(pNumber);
    TFormulaInfo param2 = extractInfo(toShift);

    return wrap(shiftLeft(param1, param2));
  }

  protected abstract TFormulaInfo shiftLeft(TFormulaInfo pExtract, TFormulaInfo pExtract2);

  @Override
  public final BitvectorFormula concat(BitvectorFormula pNumber, BitvectorFormula pAppend) {
    TFormulaInfo param1 = extractInfo(pNumber);
    TFormulaInfo param2 = extractInfo(pAppend);

    return wrap(concat(param1, param2));
  }

  protected abstract TFormulaInfo concat(TFormulaInfo number, TFormulaInfo pAppend);

  @Override
  public final BitvectorFormula extract(
      BitvectorFormula pNumber, int pMsb, int pLsb, boolean pSigned) {
    TFormulaInfo param = extractInfo(pNumber);

    return wrap(extract(param, pMsb, pLsb, pSigned));
  }

  protected abstract TFormulaInfo extract(
      TFormulaInfo pNumber, int pMsb, int pLsb, boolean pSigned);

  @Override
  public final BitvectorFormula extend(
      BitvectorFormula pNumber, int pExtensionBits, boolean pSigned) {
    TFormulaInfo param = extractInfo(pNumber);

    return wrap(extend(param, pExtensionBits, pSigned));
  }

  protected abstract TFormulaInfo extend(TFormulaInfo pNumber, int pExtensionBits, boolean pSigned);

  @Override
  public int getLength(BitvectorFormula pNumber) {
    FormulaType<BitvectorFormula> type = getFormulaCreator().getFormulaType(pNumber);
    return ((FormulaType.BitvectorType) type).getSize();
  }
}
