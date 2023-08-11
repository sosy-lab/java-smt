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

import com.google.common.base.Preconditions;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.text.Normalizer.Form;
import java.util.List;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Context;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable.Type;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.dreal;

public abstract class DReal4NumeralFormulaManager<
    ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
    DRealTerm<?>, Variable.Type, Context, ParamFormulaType, ResultFormulaType, DRealTerm<?>> {

  DReal4NumeralFormulaManager(
      DReal4FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected boolean isNumeral(DRealTerm<?> val) {
    if (val.isExp()) {
      return val.getExpression().get_kind() == ExpressionKind.Constant;
    } else {
      return false;
    }
  }

  @Override
  protected DRealTerm<Expression> makeNumberImpl(long i) {
    return new DRealTerm<>(new Expression(i), getNumeralType());
  }

  @Override
  protected DRealTerm<Expression> makeNumberImpl(BigInteger i) {
    return makeNumberImpl(i.toString());
  }

  @Override
  protected DRealTerm<Expression> makeNumberImpl(String i) {
    double d;
    if (i.contains("/")) {
      String[] rat = i.split("/", -1);
      d = Double.parseDouble(rat[0]) / Double.parseDouble(rat[1]);

    } else {
      d = Double.parseDouble(i);
    }
    return new DRealTerm<>(new Expression(d), getNumeralType());
  }

  protected abstract Variable.Type getNumeralType();

  @Override
  protected DRealTerm<Expression> makeNumberImpl(double pNumber) {
    return new DRealTerm<>(new Expression(pNumber), getNumeralType());
  }

  @Override
  protected DRealTerm<Expression> makeNumberImpl(BigDecimal pNumber) {
    return makeNumberImpl(pNumber.toString());
  }

  @Override
  protected DRealTerm<?> makeVariableImpl(String i) {
    return getFormulaCreator().makeVariable(getNumeralType(), i);
  }

  @Override
  protected DRealTerm<Expression> negate(DRealTerm<?> pParam1) {
    // Only Expression or Variables are expected
    Preconditions.checkState(pParam1.isVar() || pParam1.isExp());
    if (pParam1.isVar()) {
      return new DRealTerm<>(dreal.pow(new Expression(pParam1.getVariable()), new Expression(-1))
          , pParam1.getType());
    } else {
      return new DRealTerm<>(dreal.pow(pParam1.getExpression(), new Expression(-1)),
          pParam1.getType());
    }
  }

  @Override
  protected DRealTerm<Expression> add(DRealTerm<?> pParam1,
                                                      DRealTerm<?> pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(dreal.Add(pParam1.getExpression(), pParam2.getExpression()),
          pParam1.getType());
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(dreal.Add(new Expression(pParam1.getVariable()),
          new Expression(pParam2.getVariable())), pParam1.getType());
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(dreal.Add(pParam1.getExpression(),
          new Expression(pParam2.getVariable())), pParam1.getType());
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(dreal.Add(new Expression(pParam1.getVariable()),
          pParam2.getExpression()), pParam1.getType());
    } else {
      throw new UnsupportedOperationException("dReal does not support add on Formulas.");
    }
  }

  @Override
  protected DRealTerm<Expression> subtract(DRealTerm<?> pParam1,
                                                           DRealTerm<?> pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(dreal.Substract(pParam1.getExpression(),
          pParam2.getExpression()), pParam1.getType());
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(dreal.Substract(new Expression(pParam1.getVariable()),
          new Expression(pParam2.getVariable())), pParam1.getType());
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(dreal.Substract(pParam1.getExpression(),
          new Expression(pParam2.getVariable())), pParam1.getType());
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(dreal.Substract(new Expression(pParam1.getVariable()),
          pParam2.getExpression()), pParam1.getType());
    } else {
      throw new UnsupportedOperationException("dReal does not support subtract on Variables or "
          + "Formulas.");
    }
  }

  @Override
  public DRealTerm<Expression> divide(DRealTerm<?> pParam1,
                                                      DRealTerm<?> pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(dreal.Divide(pParam1.getExpression(), pParam2.getExpression()),
          pParam1.getType());
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(dreal.Divide(new Expression(pParam1.getVariable()),
          pParam2.getExpression()), pParam1.getType());
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(dreal.Divide(pParam1.getExpression(),
          new Expression(pParam2.getVariable())), pParam1.getType());
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(dreal.Divide(new Expression(pParam1.getVariable()),
          new Expression(pParam2.getVariable())), pParam1.getType());
    } else {
      throw new UnsupportedOperationException("dReal does not support divide with Formulas.");
    }
  }

  @Override
  public DRealTerm<Expression> multiply(DRealTerm<?> pParam1,
                                                        DRealTerm<?> pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(dreal.Multiply(pParam1.getExpression(), pParam2.getExpression()),
          pParam1.getType());
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(dreal.Multiply(new Expression(pParam1.getVariable()),
          pParam2.getExpression()), pParam1.getType());
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(dreal.Multiply(pParam1.getExpression(),
          new Expression(pParam2.getVariable())), pParam1.getType());
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(dreal.Multiply(new Expression(pParam1.getVariable()),
          new Expression(pParam2.getVariable())), pParam1.getType());
    } else {
      throw new UnsupportedOperationException("dReal does not support multiply with Formulas.");
    }
  }

  // only use Equal(Expression exp1, Expression exp2), Equal with Formulas is same as iff
  @Override
  protected DRealTerm<Formula> equal(DRealTerm<?> pParam1, DRealTerm<?> pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(dreal.Equal(pParam1.getExpression(),
          pParam2.getExpression()), Variable.Type.BOOLEAN);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(dreal.Equal(new Expression(pParam1.getVariable()),
          new Expression(pParam2.getVariable())), Variable.Type.BOOLEAN);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(dreal.Equal(pParam1.getExpression(),
          new Expression(pParam2.getVariable())), Variable.Type.BOOLEAN);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(dreal.Equal(new Expression(pParam1.getVariable()),
          pParam2.getExpression()), Variable.Type.BOOLEAN);
    } else {
      throw new UnsupportedOperationException("dReal does not support equal on Formulas.");
    }
  }


  @Override
  protected DRealTerm<Formula> distinctImpl(List<DRealTerm<?>> pNumbers) {
    // dReal does not directly support this method, so we need to build the whole term
    Formula andFormula = helperFunction(pNumbers.get(1), pNumbers.get(0));
    for (int i = 2; i < pNumbers.size(); i++) {
      for (int j = 0; j < i; j++) {
        andFormula = dreal.And(andFormula, helperFunction(pNumbers.get(i), pNumbers.get(j)));
      }
    }
    return new DRealTerm<>(andFormula, Variable.Type.BOOLEAN);
  }

  // Takes two DRealTerms and creates a NotEqual Formula to use in distinctImpl
  private Formula helperFunction(DRealTerm<?> pTerm1, DRealTerm<?> pTerm2) {
    if (pTerm1.isVar() && pTerm2.isVar()) {
      return dreal.NotEqual(pTerm1.getVariable(), pTerm2.getVariable());
    } else if (pTerm1.isExp() && pTerm2.isVar()) {
      return dreal.NotEqual(pTerm1.getExpression(),
          new Expression(pTerm2.getVariable()));
    } else if (pTerm1.isVar() && pTerm2.isExp()) {
      return dreal.NotEqual(new Expression(pTerm1.getVariable()),
          pTerm2.getExpression());
    } else if (pTerm1.isExp() && pTerm2.isExp()) {
      return dreal.NotEqual(pTerm1.getExpression(),
          pTerm2.getExpression());
    } else {
      throw new UnsupportedOperationException("dReal does not support distinctImpl on Formulas.");
    }
  }

  @Override
  protected DRealTerm<Formula> greaterThan(DRealTerm<?> pParam1,
                                                        DRealTerm<?> pParam2) {
    if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(dreal.Grater(new Expression(pParam1.getVariable()),
          new Expression(pParam2.getVariable())), Variable.Type.BOOLEAN);
    } else if(pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(dreal.Grater(new Expression(pParam1.getVariable()),
          pParam2.getExpression()), Variable.Type.BOOLEAN);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(dreal.Grater(pParam1.getExpression(),
          new Expression(pParam2.getVariable())), Variable.Type.BOOLEAN);
    } else if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(dreal.Grater(pParam1.getExpression(),
          pParam2.getExpression()), Variable.Type.BOOLEAN);
    } else {
      throw new UnsupportedOperationException("dReal does not support greaterThan on Formulas.");
    }
  }

  @Override
  protected DRealTerm<Formula> greaterOrEquals(DRealTerm<?> pParam1,
                                                            DRealTerm<?> pParam2) {
    if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(dreal.GraterEqual(new Expression(pParam1.getVariable()),
          new Expression(pParam2.getVariable())), Variable.Type.BOOLEAN);
    } else if(pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(dreal.GraterEqual(new Expression(pParam1.getVariable()),
          pParam2.getExpression()), Variable.Type.BOOLEAN);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(dreal.GraterEqual(pParam1.getExpression(),
          new Expression(pParam2.getVariable())), Variable.Type.BOOLEAN);
    } else if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(dreal.GraterEqual(pParam1.getExpression(),
          pParam2.getExpression()), Variable.Type.BOOLEAN);
    } else {
      throw new UnsupportedOperationException("dReal does not support greaterOrEquals on Formulas"
          + ".");
    }
  }

  @Override
  protected DRealTerm<Formula> lessThan(DRealTerm<?> pParam1,
                                                     DRealTerm<?> pParam2) {
    if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(dreal.Less(new Expression(pParam1.getVariable()),
          new Expression(pParam2.getVariable())), Variable.Type.BOOLEAN);
    } else if(pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(dreal.Less(new Expression(pParam1.getVariable()),
          pParam2.getExpression()), Variable.Type.BOOLEAN);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(dreal.Less(pParam1.getExpression(),
          new Expression(pParam2.getVariable())), Variable.Type.BOOLEAN);
    } else if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(dreal.Less(pParam1.getExpression(),
          pParam2.getExpression()), Variable.Type.BOOLEAN);
    } else {
      throw new UnsupportedOperationException("dReal does not support lessThan on Formulas.");
    }
  }

  @Override
  protected DRealTerm<Formula> lessOrEquals(DRealTerm<?> pParam1,
                                                         DRealTerm<?> pParam2) {
    if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(dreal.LessEqual(new Expression(pParam1.getVariable()),
          new Expression(pParam2.getVariable())), Variable.Type.BOOLEAN);
    } else if(pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(dreal.LessEqual(new Expression(pParam1.getVariable()),
          pParam2.getExpression()), Variable.Type.BOOLEAN);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(dreal.LessEqual(pParam1.getExpression(),
          new Expression(pParam2.getVariable())), Variable.Type.BOOLEAN);
    } else if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(dreal.LessEqual(pParam1.getExpression(),
          pParam2.getExpression()), Variable.Type.BOOLEAN);
    } else {
      throw new UnsupportedOperationException("dReal does not support lessOrEquals on Formulas.");
    }
  }
}
