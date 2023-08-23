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
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Dreal;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;

@SuppressWarnings("ClassTypeParameterName")
public abstract class DReal4NumeralFormulaManager<
        ParamFormulaType extends NumeralFormula, ResultFormulaType extends NumeralFormula>
    extends AbstractNumeralFormulaManager<
        DRealTerm<?, ?>,
        Variable.Type.Kind,
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
      return val.getExpression().getKind() == ExpressionKind.CONSTANT;
    } else {
      return false;
    }
  }

  @Override
  protected DRealTerm<Expression, ExpressionKind.ExpressionType> makeNumberImpl(long i) {
    return new DRealTerm<>(new Expression(i), getNumeralType(), ExpressionKind.CONSTANT);
  }

  // makeNumberImpl with BigInteger to create a constant in an integerFormula can cause a
  // problem, because dReal can not handle BigInteger in integer formulas, only in real formulas.
  @Override
  protected DRealTerm<Expression, ExpressionKind.ExpressionType> makeNumberImpl(BigInteger i) {
    return makeNumberImpl(i.toString());
  }

  @Override
  protected DRealTerm<Expression, ExpressionKind.ExpressionType> makeNumberImpl(String i) {
    double d;
    if (i.contains("/")) {
      String[] rat = i.split("/", -1);
      d = Double.parseDouble(rat[0]) / Double.parseDouble(rat[1]);

    } else {
      d = Double.parseDouble(i);
    }
    return new DRealTerm<>(new Expression(d), getNumeralType(), ExpressionKind.CONSTANT);
  }

  protected abstract Variable.Type.Kind getNumeralType();

  @Override
  protected DRealTerm<Expression, ExpressionKind.ExpressionType> makeNumberImpl(double pNumber) {
    return new DRealTerm<>(new Expression(pNumber), getNumeralType(), ExpressionKind.CONSTANT);
  }

  @Override
  protected DRealTerm<Expression, ExpressionKind.ExpressionType> makeNumberImpl(
      BigDecimal pNumber) {
    return makeNumberImpl(pNumber.toString());
  }

  @Override
  protected DRealTerm<?, ?> makeVariableImpl(String i) {
    return getFormulaCreator().makeVariable(getNumeralType(), i);
  }

  @Override
  protected DRealTerm<Expression, ExpressionKind.ExpressionType> negate(DRealTerm<?, ?> pParam1) {
    // Only Expression or Variables are expected
    Preconditions.checkState(pParam1.isVar() || pParam1.isExp());
    if (pParam1.isVar()) {
      return new DRealTerm<>(
          Dreal.pow(new Expression(pParam1.getVariable()), new Expression(-1)),
          pParam1.getType(),
          ExpressionKind.POW);
    } else {
      return new DRealTerm<>(
          Dreal.pow(pParam1.getExpression(), new Expression(-1)),
          pParam1.getType(),
          ExpressionKind.POW);
    }
  }

  @Override
  protected DRealTerm<Expression, ExpressionKind.ExpressionType> add(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(
          Dreal.add(pParam1.getExpression(), pParam2.getExpression()),
          pParam1.getType(),
          ExpressionKind.ADD);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(
          Dreal.add(new Expression(pParam1.getVariable()), new Expression(pParam2.getVariable())),
          pParam1.getType(),
          ExpressionKind.ADD);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(
          Dreal.add(pParam1.getExpression(), new Expression(pParam2.getVariable())),
          pParam1.getType(),
          ExpressionKind.ADD);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(
          Dreal.add(new Expression(pParam1.getVariable()), pParam2.getExpression()),
          pParam1.getType(),
          ExpressionKind.ADD);
    } else {
      throw new UnsupportedOperationException(
          "dReal does not support to create an Add-Formula " + "from Formulas.");
    }
  }

  @Override
  protected DRealTerm<Expression, ExpressionKind.ExpressionType> subtract(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(
          Dreal.substract(pParam1.getExpression(), pParam2.getExpression()),
          pParam1.getType(),
          ExpressionKind.ADD);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(
          Dreal.substract(
              new Expression(pParam1.getVariable()), new Expression(pParam2.getVariable())),
          pParam1.getType(),
          ExpressionKind.ADD);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(
          Dreal.substract(pParam1.getExpression(), new Expression(pParam2.getVariable())),
          pParam1.getType(),
          ExpressionKind.ADD);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(
          Dreal.substract(new Expression(pParam1.getVariable()), pParam2.getExpression()),
          pParam1.getType(),
          ExpressionKind.ADD);
    } else {
      throw new UnsupportedOperationException(
          "dReal does not support to create a subtract-Formula from Formulas.");
    }
  }

  @Override
  public DRealTerm<Expression, ExpressionKind.ExpressionType> multiply(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(
          Dreal.multiply(pParam1.getExpression(), pParam2.getExpression()),
          pParam1.getType(),
          ExpressionKind.MUL);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(
          Dreal.multiply(new Expression(pParam1.getVariable()), pParam2.getExpression()),
          pParam1.getType(),
          ExpressionKind.MUL);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(
          Dreal.multiply(pParam1.getExpression(), new Expression(pParam2.getVariable())),
          pParam1.getType(),
          ExpressionKind.MUL);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(
          Dreal.multiply(
              new Expression(pParam1.getVariable()), new Expression(pParam2.getVariable())),
          pParam1.getType(),
          ExpressionKind.MUL);
    } else {
      throw new UnsupportedOperationException(
          "dReal does not support to create multiply-Formulas " + "with Formulas.");
    }
  }

  // only use Equal(Expression exp1, Expression exp2), Equal with Formulas is same as iff
  @Override
  protected DRealTerm<Formula, FormulaKind.FormulaType> equal(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(
          Dreal.equal(pParam1.getExpression(), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.EQ);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(
          Dreal.equal(new Expression(pParam1.getVariable()), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.EQ);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(
          Dreal.equal(pParam1.getExpression(), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.EQ);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(
          Dreal.equal(new Expression(pParam1.getVariable()), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.EQ);
    } else {
      throw new UnsupportedOperationException(
          "dReal does not support to create an equal-Formula " + "from Formulas.");
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind.FormulaType> distinctImpl(
      List<DRealTerm<?, ?>> pNumbers) {
    // dReal does not directly support this method, so we need to build the whole term
    Formula andFormula = helperFunction(pNumbers.get(1), pNumbers.get(0));
    for (int i = 2; i < pNumbers.size(); i++) {
      for (int j = 0; j < i; j++) {
        andFormula = Dreal.and(andFormula, helperFunction(pNumbers.get(i), pNumbers.get(j)));
      }
    }
    return new DRealTerm<>(andFormula, Variable.Type.BOOLEAN, FormulaKind.AND);
  }

  // Takes two DRealTerms and creates a NotEqual Formula to use in distinctImpl
  private Formula helperFunction(DRealTerm<?, ?> pTerm1, DRealTerm<?, ?> pTerm2) {
    if (pTerm1.isVar() && pTerm2.isVar()) {
      return Dreal.notEqual(pTerm1.getVariable(), pTerm2.getVariable());
    } else if (pTerm1.isExp() && pTerm2.isVar()) {
      return Dreal.notEqual(pTerm1.getExpression(), new Expression(pTerm2.getVariable()));
    } else if (pTerm1.isVar() && pTerm2.isExp()) {
      return Dreal.notEqual(new Expression(pTerm1.getVariable()), pTerm2.getExpression());
    } else if (pTerm1.isExp() && pTerm2.isExp()) {
      return Dreal.notEqual(pTerm1.getExpression(), pTerm2.getExpression());
    } else {
      throw new UnsupportedOperationException("dReal does not support distinctImpl on Formulas.");
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind.FormulaType> greaterThan(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(
          Dreal.grater(
              new Expression(pParam1.getVariable()), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.GT);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(
          Dreal.grater(new Expression(pParam1.getVariable()), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.GT);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(
          Dreal.grater(pParam1.getExpression(), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.GT);
    } else if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(
          Dreal.grater(pParam1.getExpression(), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.GT);
    } else {
      throw new UnsupportedOperationException(
          "dReal does not support to create a " + "greaterThan-Formula form formulas.");
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind.FormulaType> greaterOrEquals(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(
          Dreal.graterEqual(
              new Expression(pParam1.getVariable()), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.GEQ);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(
          Dreal.graterEqual(new Expression(pParam1.getVariable()), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.GEQ);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(
          Dreal.graterEqual(pParam1.getExpression(), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.GEQ);
    } else if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(
          Dreal.graterEqual(pParam1.getExpression(), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.GEQ);
    } else {
      throw new UnsupportedOperationException(
          "dReal does not support to create a greaterOrEquals-Formula from formulas.");
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind.FormulaType> lessThan(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(
          Dreal.less(new Expression(pParam1.getVariable()), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.LT);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(
          Dreal.less(new Expression(pParam1.getVariable()), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.LT);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(
          Dreal.less(pParam1.getExpression(), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.LT);
    } else if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(
          Dreal.less(pParam1.getExpression(), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.LT);
    } else {
      throw new UnsupportedOperationException(
          "dReal does not support to create a " + "lessThan-Formula from Formulas.");
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind.FormulaType> lessOrEquals(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm<>(
          Dreal.lessEqual(
              new Expression(pParam1.getVariable()), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.LEQ);
    } else if (pParam1.isVar() && pParam2.isExp()) {
      return new DRealTerm<>(
          Dreal.lessEqual(new Expression(pParam1.getVariable()), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.LEQ);
    } else if (pParam1.isExp() && pParam2.isVar()) {
      return new DRealTerm<>(
          Dreal.lessEqual(pParam1.getExpression(), new Expression(pParam2.getVariable())),
          Variable.Type.BOOLEAN,
          FormulaKind.LEQ);
    } else if (pParam1.isExp() && pParam2.isExp()) {
      return new DRealTerm<>(
          Dreal.lessEqual(pParam1.getExpression(), pParam2.getExpression()),
          Variable.Type.BOOLEAN,
          FormulaKind.LEQ);
    } else {
      throw new UnsupportedOperationException(
          "dReal does not support to create a " + "lessOrEquals-Formula from Formulas.");
    }
  }
}
