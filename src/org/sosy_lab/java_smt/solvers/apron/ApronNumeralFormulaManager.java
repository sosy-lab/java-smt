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
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulaType.Type;
import org.sosy_lab.java_smt.solvers.apron.types.ApronFormulas;

abstract class ApronNumeralFormulaManager <
    ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
    ApronFormulas, ApronFormulaType, Environment, ParamFormulaType, ResultFormulaType, Long> {
  protected ApronNumeralFormulaManager(
      FormulaCreator<ApronFormulas, ApronFormulaType, Environment, Long> pCreator,
      NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }


  protected boolean isNumeral(ApronFormulas val){
    return false;
  }
  protected abstract Type getNumeralType();
  @Override
  protected ApronFormulas makeNumberImpl(long i) {
    return null;
  }

  @Override
  protected ApronFormulas makeNumberImpl(BigInteger i) {
    return null;
  }

  @Override
  protected ApronFormulas makeNumberImpl(String i) {
    return null;
  }

  @Override
  protected ApronFormulas negate(ApronFormulas pParam1) {
    return null;
  }

  @Override
  protected ApronFormulas add(ApronFormulas pParam1, ApronFormulas pParam2) {
    return null;
  }

  @Override
  protected ApronFormulas sumImpl(List<ApronFormulas> operands){
    return null;
  }
  @Override
  protected ApronFormulas subtract(ApronFormulas pParam1, ApronFormulas pParam2) {
    return null;
  }

  @Override
  protected ApronFormulas divide(ApronFormulas pParam1, ApronFormulas pParam2) {
    return null;
  }

  @Override
  protected ApronFormulas multiply(ApronFormulas pParam1, ApronFormulas pParam2) {
    return null;
  }

  @Override
  protected ApronFormulas equal(ApronFormulas pParam1, ApronFormulas pParam2) {
    return null;
  }

  @Override
  protected ApronFormulas distinctImpl(List pNumbers) {
    return null;
  }

  @Override
  protected ApronFormulas greaterThan(ApronFormulas pParam1, ApronFormulas pParam2) {
    return null;
  }

  @Override
  protected ApronFormulas greaterOrEquals(ApronFormulas pParam1, ApronFormulas pParam2) {
    return null;
  }

  @Override
  protected ApronFormulas lessThan(ApronFormulas pParam1, ApronFormulas pParam2) {
    return null;
  }

  @Override
  protected ApronFormulas lessOrEquals(ApronFormulas pParam1, ApronFormulas pParam2) {
    return null;
  }
}
