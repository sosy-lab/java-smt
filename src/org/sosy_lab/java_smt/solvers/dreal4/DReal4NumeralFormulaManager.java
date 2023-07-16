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

package org.sosy_lab.java_smt.solvers.dreal4;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Context;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable.Type;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.dreal;

public abstract class DReal4NumeralFormulaManager<
    ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
    DRealTerm, Type, Context, ParamFormulaType, ResultFormulaType, DRealTerm> {

  DReal4NumeralFormulaManager(
      DReal4FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  public FormulaType<ResultFormulaType> getFormulaType() {
    return null;
  }

  @Override
  protected boolean isNumeral(DRealTerm val) {
    if (val.isExp()) {
      return val.getExpression().get_kind() == ExpressionKind.Constant;
    } else {
      throw new UnsupportedOperationException("dReal does not support isNumeral on Variable or "
          + "Formula.");
    }
  }

  @Override
  protected DRealTerm makeNumberImpl(long i) {
    return null;
  }

  @Override
  protected DRealTerm makeNumberImpl(BigInteger i) {
    return null;
  }

  @Override
  protected DRealTerm makeNumberImpl(String i) {
    return null;
  }

  protected abstract Type getNumeralType();

  @Override
  protected DRealTerm makeNumberImpl(double pNumber) {
    return new DRealTerm(null, new Expression(pNumber), null);
  }

  @Override
  protected DRealTerm makeNumberImpl(BigDecimal pNumber) {
    return null;
  }

  @Override
  protected DRealTerm makeVariableImpl(String i) {
    return getFormulaCreator().makeVariable(getNumeralType(), i);
  }

  @Override
  protected DRealTerm negate(DRealTerm pParam1) {
    return null;
  }

  @Override
  protected DRealTerm add(DRealTerm pParam1, DRealTerm pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm(null, dreal.Add(pParam1.getExpression(), pParam2.getExpression()), null);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm(null, dreal.Add(new Expression(pParam1.getVariable()),
          new Expression(pParam1.getVariable())), null);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm(null, dreal.Add(pParam1.getExpression(),
          new Expression(pParam2.getVariable())), null);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm(null, dreal.Add(new Expression(pParam1.getVariable()),
          pParam2.getExpression()), null);
    } else {
      throw new UnsupportedOperationException("dReal does not support add on Formulas.");
    }
  }

  @Override
  protected DRealTerm subtract(DRealTerm pParam1, DRealTerm pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm(null, dreal.Substract(pParam1.getExpression(), pParam2.getExpression()), null);
    } else {
      throw new UnsupportedOperationException("dReal does not support subtract on Variables or "
          + "Formulas.");
    }
  }

  @Override
  public DRealTerm divide(DRealTerm pParam1, DRealTerm pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm(null, dreal.Divide(pParam1.getExpression(), pParam2.getExpression()),
          null);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm(null, dreal.Divide(new Expression(pParam1.getVariable()),
          pParam2.getExpression()), null);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm(null, dreal.Divide(pParam1.getExpression(),
          new Expression(pParam2.getVariable())), null);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm(null, dreal.Divide(new Expression(pParam1.getVariable()),
          new Expression(pParam2.getVariable())), null);
    } else {
      throw new UnsupportedOperationException("dReal does not support divide with Formulas.");
    }
  }

  @Override
  public DRealTerm multiply(DRealTerm pParam1, DRealTerm pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm(null, dreal.Multiply(pParam1.getExpression(), pParam2.getExpression()),
          null);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm(null, dreal.Multiply(new Expression(pParam1.getVariable()),
          pParam2.getExpression()), null);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm(null, dreal.Multiply(pParam1.getExpression(),
          new Expression(pParam2.getVariable())), null);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm(null, dreal.Multiply(new Expression(pParam1.getVariable()),
          new Expression(pParam2.getVariable())), null);
    } else {
      throw new UnsupportedOperationException("dReal does not support multiply with Formulas.");
    }
  }

  // only use Equal(Expression exp1, Expression exp2), Equal with Formulas is same as iff
  @Override
  protected DRealTerm equal(DRealTerm pParam1, DRealTerm pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm(null, null, dreal.Equal(pParam1.getExpression(),
          pParam2.getExpression()));
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm(null, null, dreal.Equal(new Expression(pParam1.getVariable()),
          new Expression(pParam2.getVariable())));
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm(null, null, dreal.Equal(pParam1.getExpression(),
          new Expression(pParam2.getVariable())));
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm(null, null, dreal.Equal(pParam1.getExpression(),
          new Expression(pParam2.getVariable())));
    } else {
      throw new UnsupportedOperationException("dReal does not support equal on Formulas.");
    }
  }


  @Override
  protected DRealTerm distinctImpl(List<DRealTerm> pNumbers) {
    return null;
  }

  @Override
  protected DRealTerm greaterThan(DRealTerm pParam1, DRealTerm pParam2) {
    if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm(null, null, dreal.Grater(new Expression(pParam1.getVariable()),
          new Expression(pParam2.getVariable())));
    } else if(pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm(null, null, dreal.Grater(new Expression(pParam1.getVariable()),
          pParam2.getExpression()));
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm(null, null, dreal.Grater(pParam1.getExpression(),
          new Expression(pParam2.getVariable())));
    } else if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm(null, null, dreal.Grater(pParam1.getExpression(),
          pParam2.getExpression()));
    } else {
      throw new UnsupportedOperationException("dReal does not support greaterThan on Formulas.");
    }
  }

  @Override
  protected DRealTerm greaterOrEquals(DRealTerm pParam1, DRealTerm pParam2) {
    if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm(null, null, dreal.GraterEqual(new Expression(pParam1.getVariable()),
          new Expression(pParam2.getVariable())));
    } else if(pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm(null, null, dreal.GraterEqual(new Expression(pParam1.getVariable()),
          pParam2.getExpression()));
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm(null, null, dreal.GraterEqual(pParam1.getExpression(),
          new Expression(pParam2.getVariable())));
    } else if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm(null, null, dreal.GraterEqual(pParam1.getExpression(),
          pParam2.getExpression()));
    } else {
      throw new UnsupportedOperationException("dReal does not support greaterOrEquals on Formulas"
          + ".");
    }
  }

  @Override
  protected DRealTerm lessThan(DRealTerm pParam1, DRealTerm pParam2) {
    if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm(null, null, dreal.Less(new Expression(pParam1.getVariable()),
          new Expression(pParam2.getVariable())));
    } else if(pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm(null, null, dreal.Less(new Expression(pParam1.getVariable()),
          pParam2.getExpression()));
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm(null, null, dreal.Less(pParam1.getExpression(),
          new Expression(pParam2.getVariable())));
    } else if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm(null, null, dreal.Less(pParam1.getExpression(),
          pParam2.getExpression()));
    } else {
      throw new UnsupportedOperationException("dReal does not support lessThan on Formulas.");
    }
  }

  @Override
  protected DRealTerm lessOrEquals(DRealTerm pParam1, DRealTerm pParam2) {
    if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm(null, null, dreal.LessEqual(new Expression(pParam1.getVariable()),
          new Expression(pParam2.getVariable())));
    } else if(pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm(null, null, dreal.LessEqual(new Expression(pParam1.getVariable()),
          pParam2.getExpression()));
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm(null, null, dreal.LessEqual(pParam1.getExpression(),
          new Expression(pParam2.getVariable())));
    } else if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm(null, null, dreal.LessEqual(pParam1.getExpression(),
          pParam2.getExpression()));
    } else {
      throw new UnsupportedOperationException("dReal does not support lessOrEquals on Formulas.");
    }
  }
}
