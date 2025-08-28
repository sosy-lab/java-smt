// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import static scala.collection.JavaConverters.asScala;

import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.ITerm;
import ap.types.Sort;
import com.google.common.collect.Iterables;
import java.util.List;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;

@SuppressWarnings("ClassTypeParameterName")
abstract class PrincessNumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
        IExpression,
        Sort,
        PrincessEnvironment,
        ParamFormulaType,
        ResultFormulaType,
        PrincessFunctionDeclaration> {

  PrincessNumeralFormulaManager(
      PrincessFormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected IFormula equal(IExpression pNumber1, IExpression pNumber2) {
    return ((ITerm) pNumber1).$eq$eq$eq((ITerm) pNumber2);
  }

  @Override
  protected IExpression distinctImpl(List<IExpression> pNumbers) {
    return IExpression.distinct(asScala(Iterables.filter(pNumbers, ITerm.class)));
  }

  @Override
  public IExpression toRational(IExpression formula) {
    return PrincessEnvironment.rationalTheory.int2ring((ITerm) formula);
  }
}
