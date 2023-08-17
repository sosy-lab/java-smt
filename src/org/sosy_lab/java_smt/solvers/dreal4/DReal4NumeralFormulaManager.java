// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.dreal4;

import com.google.common.base.Preconditions;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractNumeralFormulaManager;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Config;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.dreal;

public abstract class DReal4NumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
        DRealTerm<?, ?>,
        Variable.Type,
        Config,
        ParamFormulaType,
        ResultFormulaType,
        DRealTerm<?, ?>> {

  DReal4NumeralFormulaManager(
      DReal4FormulaCreator pCreator, NonLinearArithmetic pNonLinearArithmetic) {
    super(pCreator, pNonLinearArithmetic);
  }

  @Override
  protected boolean isNumeral(DRealTerm<?, ?> val) {
    if (val.isExp()) {
      return val.getExpression().get_kind() == ExpressionKind.Constant;
    } else {
      return false;
    }
  }

  @Override
  protected DRealTerm<Expression, ExpressionKind> makeNumberImpl(long i) {
    return new DRealTerm<>(new Expression(i), getNumeralType(), ExpressionKind.Constant);
  }

  // makeNumberImpl with BigInteger to create a constant in an integerFormula can cause a
  // problem, because dReal can not handle BigInteger in integer formulas, only in real formulas.
  @Override
  protected DRealTerm<Expression, ExpressionKind> makeNumberImpl(BigInteger i) {
    return makeNumberImpl(i.toString());
  }

  @Override
  protected DRealTerm<Expression, ExpressionKind> makeNumberImpl(String i) {
    double d;
    if (i.contains("/")) {
      String[] rat = i.split("/", -1);
      d = Double.parseDouble(rat[0]) / Double.parseDouble(rat[1]);

    } else {
      d = Double.parseDouble(i);
    }
    return new DRealTerm<>(new Expression(d), getNumeralType(), ExpressionKind.Constant);
  }

  protected abstract Variable.Type getNumeralType();

  @Override
  protected DRealTerm<Expression, ExpressionKind> makeNumberImpl(double pNumber) {
    return new DRealTerm<>(new Expression(pNumber), getNumeralType(), ExpressionKind.Constant);
  }

  @Override
  protected DRealTerm<Expression, ExpressionKind> makeNumberImpl(BigDecimal pNumber) {
    return makeNumberImpl(pNumber.toString());
  }

  @Override
  protected DRealTerm<?, ?> makeVariableImpl(String i) {
    return getFormulaCreator().makeVariable(getNumeralType(), i);
  }

  @Override
  protected DRealTerm<Expression, ExpressionKind> negate(DRealTerm<?, ?> pParam1) {
    // Only Expression or Variables are expected
    Preconditions.checkState(pParam1.isVar() || pParam1.isExp());
    if (pParam1.isVar()) {
      return new DRealTerm<>(
          dreal.pow(new Expression(pParam1.getVariable()), new Expression(-1)),
          pParam1.getType(),
          ExpressionKind.Pow);
    } else {
      return new DRealTerm<>(
          dreal.pow(pParam1.getExpression(), new Expression(-1)),
          pParam1.getType(),
          ExpressionKind.Pow);
    }
  }

  @Override
  protected DRealTerm<Expression, ExpressionKind> add(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(
          dreal.Add(pParam1.getExpression(), pParam2.getExpression()),
          pParam1.getType(),
          ExpressionKind.Add);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(
          dreal.Add(new Expression(pParam1.getVariable()), new Expression(pParam2.getVariable())),
          pParam1.getType(),
          ExpressionKind.Add);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(
          dreal.Add(pParam1.getExpression(), new Expression(pParam2.getVariable())),
          pParam1.getType(),
          ExpressionKind.Add);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(
          dreal.Add(new Expression(pParam1.getVariable()), pParam2.getExpression()),
          pParam1.getType(),
          ExpressionKind.Add);
    } else {
      throw new UnsupportedOperationException(
          "dReal does not support to create an Add-Formula " + "from Formulas.");
    }
  }

  @Override
  protected DRealTerm<Expression, ExpressionKind> subtract(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(
          dreal.Substract(pParam1.getExpression(), pParam2.getExpression()),
          pParam1.getType(),
          ExpressionKind.Add);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(
          dreal.Substract(
              new Expression(pParam1.getVariable()), new Expression(pParam2.getVariable())),
          pParam1.getType(),
          ExpressionKind.Add);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(
          dreal.Substract(pParam1.getExpression(), new Expression(pParam2.getVariable())),
          pParam1.getType(),
          ExpressionKind.Add);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(
          dreal.Substract(new Expression(pParam1.getVariable()), pParam2.getExpression()),
          pParam1.getType(),
          ExpressionKind.Add);
    } else {
      throw new UnsupportedOperationException(
          "dReal does not support to create a subtract-Formula from Formulas.");
    }
  }

  @Override
  public DRealTerm<Expression, ExpressionKind> multiply(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(
          dreal.Multiply(pParam1.getExpression(), pParam2.getExpression()),
          pParam1.getType(),
          ExpressionKind.Mul);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(
          dreal.Multiply(new Expression(pParam1.getVariable()), pParam2.getExpression()),
          pParam1.getType(),
          ExpressionKind.Mul);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(
          dreal.Multiply(pParam1.getExpression(), new Expression(pParam2.getVariable())),
          pParam1.getType(),
          ExpressionKind.Mul);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(
          dreal.Multiply(
              new Expression(pParam1.getVariable()), new Expression(pParam2.getVariable())),
          pParam1.getType(),
          ExpressionKind.Mul);
    } else {
      throw new UnsupportedOperationException(
          "dReal does not support to create multiply-Formulas " + "with Formulas.");
    }
  }

  // only use Equal(Expression exp1, Expression exp2), Equal with Formulas is same as iff
  @Override
  protected DRealTerm<Formula, FormulaKind> equal(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(
          dreal.Equal(pParam1.getExpression(), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.Eq);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(
          dreal.Equal(new Expression(pParam1.getVariable()), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.Eq);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(
          dreal.Equal(pParam1.getExpression(), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.Eq);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(
          dreal.Equal(new Expression(pParam1.getVariable()), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.Eq);
    } else {
      throw new UnsupportedOperationException(
          "dReal does not support to create an equal-Formula " + "from Formulas.");
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind> distinctImpl(List<DRealTerm<?, ?>> pNumbers) {
    // dReal does not directly support this method, so we need to build the whole term
    Formula andFormula = helperFunction(pNumbers.get(1), pNumbers.get(0));
    for (int i = 2; i < pNumbers.size(); i++) {
      for (int j = 0; j < i; j++) {
        andFormula = dreal.And(andFormula, helperFunction(pNumbers.get(i), pNumbers.get(j)));
      }
    }
    return new DRealTerm<>(andFormula, Variable.Type.BOOLEAN, FormulaKind.And);
  }

  // Takes two DRealTerms and creates a NotEqual Formula to use in distinctImpl
  private Formula helperFunction(DRealTerm<?, ?> pTerm1, DRealTerm<?, ?> pTerm2) {
    if (pTerm1.isVar() && pTerm2.isVar()) {
      return dreal.NotEqual(pTerm1.getVariable(), pTerm2.getVariable());
    } else if (pTerm1.isExp() && pTerm2.isVar()) {
      return dreal.NotEqual(pTerm1.getExpression(), new Expression(pTerm2.getVariable()));
    } else if (pTerm1.isVar() && pTerm2.isExp()) {
      return dreal.NotEqual(new Expression(pTerm1.getVariable()), pTerm2.getExpression());
    } else if (pTerm1.isExp() && pTerm2.isExp()) {
      return dreal.NotEqual(pTerm1.getExpression(), pTerm2.getExpression());
    } else {
      throw new UnsupportedOperationException("dReal does not support distinctImpl on Formulas.");
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind> greaterThan(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(
          dreal.Grater(
              new Expression(pParam1.getVariable()), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.Gt);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(
          dreal.Grater(new Expression(pParam1.getVariable()), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.Gt);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(
          dreal.Grater(pParam1.getExpression(), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.Gt);
    } else if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(
          dreal.Grater(pParam1.getExpression(), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.Gt);
    } else {
      throw new UnsupportedOperationException(
          "dReal does not support to create a " + "greaterThan-Formula form formulas.");
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind> greaterOrEquals(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(
          dreal.GraterEqual(
              new Expression(pParam1.getVariable()), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.Geq);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(
          dreal.GraterEqual(new Expression(pParam1.getVariable()), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.Geq);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(
          dreal.GraterEqual(pParam1.getExpression(), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.Geq);
    } else if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(
          dreal.GraterEqual(pParam1.getExpression(), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.Geq);
    } else {
      throw new UnsupportedOperationException(
          "dReal does not support to create a greaterOrEquals-Formula from formulas.");
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind> lessThan(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(
          dreal.Less(new Expression(pParam1.getVariable()), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.Lt);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(
          dreal.Less(new Expression(pParam1.getVariable()), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.Lt);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(
          dreal.Less(pParam1.getExpression(), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.Lt);
    } else if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(
          dreal.Less(pParam1.getExpression(), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.Lt);
    } else {
      throw new UnsupportedOperationException(
          "dReal does not support to create a " + "lessThan-Formula from Formulas.");
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind> lessOrEquals(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(
          dreal.LessEqual(
              new Expression(pParam1.getVariable()), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.Leq);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(
          dreal.LessEqual(new Expression(pParam1.getVariable()), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.Leq);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(
          dreal.LessEqual(pParam1.getExpression(), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.Leq);
    } else if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(
          dreal.LessEqual(pParam1.getExpression(), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.Leq);
    } else {
      throw new UnsupportedOperationException(
          "dReal does not support to create a " + "lessOrEquals-Formula from Formulas.");
    }
  }
}
