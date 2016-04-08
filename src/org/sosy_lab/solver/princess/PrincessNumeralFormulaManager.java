/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.solver.princess;

import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.ITerm;

import org.sosy_lab.solver.api.NumeralFormula;
import org.sosy_lab.solver.basicimpl.AbstractNumeralFormulaManager;

abstract class PrincessNumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
        IExpression, PrincessTermType, PrincessEnvironment, ParamFormulaType, ResultFormulaType,
        PrincessFunctionDeclaration> {

  PrincessNumeralFormulaManager(PrincessFormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  public ITerm negate(IExpression pNumber) {
    return ((ITerm) pNumber).unary_$minus();
  }

  @Override
  public ITerm add(IExpression pNumber1, IExpression pNumber2) {
    return ((ITerm) pNumber1).$plus((ITerm) pNumber2);
  }

  @Override
  public ITerm subtract(IExpression pNumber1, IExpression pNumber2) {
    return ((ITerm) pNumber1).$minus((ITerm) pNumber2);
  }

  @Override
  public IFormula equal(IExpression pNumber1, IExpression pNumber2) {
    return ((ITerm) pNumber1).$eq$eq$eq((ITerm) pNumber2);
  }

  @Override
  public IFormula greaterThan(IExpression pNumber1, IExpression pNumber2) {
    return ((ITerm) pNumber1).$greater((ITerm) pNumber2);
  }

  @Override
  public IFormula greaterOrEquals(IExpression pNumber1, IExpression pNumber2) {
    return ((ITerm) pNumber1).$greater$eq((ITerm) pNumber2);
  }

  @Override
  public IFormula lessThan(IExpression pNumber1, IExpression pNumber2) {
    return ((ITerm) pNumber1).$less((ITerm) pNumber2);
  }

  @Override
  public IFormula lessOrEquals(IExpression pNumber1, IExpression pNumber2) {
    return ((ITerm) pNumber1).$less$eq((ITerm) pNumber2);
  }
}
