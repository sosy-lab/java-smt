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
import java.math.BigDecimal;
import java.math.BigInteger;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;

class SmtInterpolRationalFormulaManager
    extends SmtInterpolNumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {

  SmtInterpolRationalFormulaManager(SmtInterpolFormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected Term makeNumberImpl(long i) {
    return getFormulaCreator().getEnv().decimal(BigDecimal.valueOf(i));
  }

  @Override
  protected Term makeNumberImpl(BigInteger pI) {
    return getFormulaCreator().getEnv().decimal(new BigDecimal(pI));
  }

  @Override
  protected Term makeNumberImpl(String pI) {
    return getFormulaCreator().getEnv().decimal(pI);
  }

  @Override
  protected Term makeNumberImpl(Rational pI) {
    return getFormulaCreator().getEnv().getTheory().rational(pI.getNum(), pI.getDen());
  }

  @Override
  protected Term makeNumberImpl(double pNumber) {
    return getFormulaCreator().getEnv().decimal(BigDecimal.valueOf(pNumber));
  }

  @Override
  protected Term makeNumberImpl(BigDecimal pNumber) {
    return getFormulaCreator().getEnv().decimal(pNumber);
  }

  @Override
  protected Term makeVariableImpl(String varName) {
    Sort t = getFormulaCreator().getRationalType();
    return getFormulaCreator().makeVariable(t, varName);
  }

  @Override
  public Term divide(Term pNumber1, Term pNumber2) {
    if (isNumeral(pNumber2)) {
      Sort intSort = pNumber1.getTheory().getNumericSort();
      Sort realSort = pNumber1.getTheory().getRealSort();
      assert intSort.equals(pNumber1.getSort()) || realSort.equals(pNumber1.getSort());
      assert intSort.equals(pNumber2.getSort()) || realSort.equals(pNumber2.getSort());
      return getFormulaCreator().getEnv().term("/", pNumber1, pNumber2);
    } else {
      return super.divide(pNumber1, pNumber2);
    }
  }
}
