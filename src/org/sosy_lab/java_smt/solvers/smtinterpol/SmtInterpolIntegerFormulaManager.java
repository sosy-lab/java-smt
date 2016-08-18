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
package org.sosy_lab.java_smt.solvers.smtinterpol;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

import java.math.BigDecimal;
import java.math.BigInteger;

class SmtInterpolIntegerFormulaManager
    extends SmtInterpolNumeralFormulaManager<IntegerFormula, IntegerFormula>
    implements IntegerFormulaManager {

  SmtInterpolIntegerFormulaManager(SmtInterpolFormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected Term makeNumberImpl(long i) {
    return getFormulaCreator().getEnv().numeral(BigInteger.valueOf(i));
  }

  @Override
  protected Term makeNumberImpl(BigInteger pI) {
    return getFormulaCreator().getEnv().numeral(pI);
  }

  @Override
  protected Term makeNumberImpl(String pI) {
    return getFormulaCreator().getEnv().numeral(pI);
  }

  @Override
  protected Term makeNumberImpl(double pNumber) {
    return makeNumberImpl((long) pNumber);
  }

  @Override
  protected Term makeNumberImpl(BigDecimal pNumber) {
    return decimalAsInteger(pNumber);
  }

  @Override
  protected Term makeVariableImpl(String varName) {
    Sort t = getFormulaCreator().getIntegerType();
    return getFormulaCreator().makeVariable(t, varName);
  }

  @Override
  public Term divide(Term pNumber1, Term pNumber2) {
    if (isNumeral(pNumber2)) {
      Sort intSort = pNumber1.getTheory().getNumericSort();
      assert intSort.equals(pNumber1.getSort()) && intSort.equals(pNumber2.getSort());
      return getFormulaCreator().getEnv().term("div", pNumber1, pNumber2);
    } else {
      return super.divide(pNumber1, pNumber2);
    }
  }

  @Override
  protected Term modulo(Term pNumber1, Term pNumber2) {
    if (isNumeral(pNumber2)) {
      Sort intSort = pNumber1.getTheory().getNumericSort();
      assert intSort.equals(pNumber1.getSort()) && intSort.equals(pNumber2.getSort());
      return getFormulaCreator().getEnv().term("mod", pNumber1, pNumber2);
    } else {
      return super.modulo(pNumber1, pNumber2);
    }
  }
}
