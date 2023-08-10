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

import java.math.BigDecimal;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.ApronRationalType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.FormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulas;

public class ApronRationalFormulaManager extends
                                         ApronNumeralFormulaManager<NumeralFormula, RationalFormula>
    implements RationalFormulaManager {

  private ApronFormulaCreator formulaCreator;
  private ApronFormulaType rationalType = new ApronRationalType();

  protected ApronRationalFormulaManager(
      ApronFormulaCreator pFormulaCreator,
      NonLinearArithmetic pNonLinearArithmetic) {
    super(pFormulaCreator, pNonLinearArithmetic);
    this.formulaCreator = pFormulaCreator;
  }
  @Override
  protected FormulaType getNumeralType() {
    return FormulaType.RATIONAL;
  }

  @Override
  protected ApronFormulas makeNumberImpl(double pNumber) {
    return null;
  }

  @Override
  protected ApronFormulas makeNumberImpl(BigDecimal pNumber) {
    return null;
  }


  @Override
  protected ApronFormulas makeVariableImpl(String i) {
    return formulaCreator.makeVariable(rationalType,i);
  }

}
