// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.dreal4;

import com.google.common.base.Preconditions;
import java.util.Collection;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Config;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Dreal;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Expression;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.ExpressionKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;

public class DReal4BooleanFormulaManager
    extends AbstractBooleanFormulaManager<
        DRealTerm<?, ?>, Variable.Type.Kind, Config, DRealTerm<?, ?>> {

  protected DReal4BooleanFormulaManager(DReal4FormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected DRealTerm<?, ?> makeVariableImpl(String pVar) {
    return formulaCreator.makeVariable(getFormulaCreator().getBoolType(), pVar);
  }

  @Override
  protected DRealTerm<Formula, FormulaKind.FormulaType> makeBooleanImpl(boolean value) {
    if (value) {
      return new DRealTerm<>(Formula.formulaTrue(), Variable.Type.BOOLEAN, FormulaKind.TRUE);
    } else {
      return new DRealTerm<>(Formula.formulaFalse(), Variable.Type.BOOLEAN, FormulaKind.FALSE);
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind.FormulaType> not(DRealTerm<?, ?> pParam1) {
    if (pParam1.isFormula()) {
      return new DRealTerm<>(
          Dreal.not(pParam1.getFormula()), Variable.Type.BOOLEAN, FormulaKind.NOT);
    } else if (pParam1.isVar()) {
      Preconditions.checkState(pParam1.getType() == Variable.Type.BOOLEAN);
      return new DRealTerm<>(
          Dreal.not(new Formula(pParam1.getVariable())), Variable.Type.BOOLEAN, FormulaKind.NOT);
    } else {
      throw new UnsupportedOperationException(
          "Dreal does not support to create a not-Formula " + "from Expressions.");
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind.FormulaType> and(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isVar() && pParam2.isFormula()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(pParam1.getType() == Variable.Type.BOOLEAN);
      return new DRealTerm<>(
          Dreal.and(pParam1.getVariable(), pParam2.getFormula()),
          Variable.Type.BOOLEAN,
          FormulaKind.AND);
    } else if (pParam1.isFormula() && pParam2.isVar()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(pParam2.getType() == Variable.Type.BOOLEAN);
      return new DRealTerm<>(
          Dreal.and(pParam1.getFormula(), pParam2.getVariable()),
          Variable.Type.BOOLEAN,
          FormulaKind.AND);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(pParam1.getType() == Variable.Type.BOOLEAN);
      Preconditions.checkState(pParam2.getType() == Variable.Type.BOOLEAN);
      return new DRealTerm<>(
          Dreal.and(pParam1.getVariable(), pParam2.getVariable()),
          Variable.Type.BOOLEAN,
          FormulaKind.AND);
    } else if (pParam1.isFormula() && pParam2.isFormula()) {
      return new DRealTerm<>(
          Dreal.and(pParam1.getFormula(), pParam2.getFormula()),
          Variable.Type.BOOLEAN,
          FormulaKind.AND);
    } else {
      throw new UnsupportedOperationException(
          "Dreal does not support to create an And-Formula " + "form Expressions.");
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind.FormulaType> andImpl(
      Collection<DRealTerm<?, ?>> pParams) {
    Formula result = Formula.formulaTrue();
    for (DRealTerm<?, ?> formula : pParams) {
      // Only Formulas or Variables of boolean type are accepted when creating an And-Formula
      Preconditions.checkState(
          formula.isFormula() || (formula.isVar() && (formula.getType() == Variable.Type.BOOLEAN)));
      if (formula.isFormula()) {
        if (formula.getFormulaKind() == FormulaKind.FALSE) {
          return new DRealTerm<>(Formula.formulaFalse(), Variable.Type.BOOLEAN, FormulaKind.FALSE);
        }
        result = Dreal.and(result, formula.getFormula());
      } else if (formula.isVar() && formula.getType() == Variable.Type.BOOLEAN) {
        result = Dreal.and(result, formula.getVariable());
      } else {
        throw new IllegalArgumentException(
            "Expression or Variable of not boolean type are not "
                + "supported to create an And-Formula.");
      }
    }
    return new DRealTerm<>(result, Variable.Type.BOOLEAN, FormulaKind.AND);
  }

  @Override
  protected DRealTerm<Formula, FormulaKind.FormulaType> or(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isVar() && pParam2.isFormula()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(pParam1.getType() == Variable.Type.BOOLEAN);
      return new DRealTerm<>(
          Dreal.or(pParam1.getVariable(), pParam2.getFormula()),
          Variable.Type.BOOLEAN,
          FormulaKind.OR);
    } else if (pParam1.isFormula() && pParam2.isVar()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(pParam2.getType() == Variable.Type.BOOLEAN);
      return new DRealTerm<>(
          Dreal.or(pParam1.getFormula(), pParam2.getVariable()),
          Variable.Type.BOOLEAN,
          FormulaKind.OR);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(pParam1.getType() == Variable.Type.BOOLEAN);
      Preconditions.checkState(pParam2.getType() == Variable.Type.BOOLEAN);
      return new DRealTerm<>(
          Dreal.or(pParam1.getVariable(), pParam2.getVariable()),
          Variable.Type.BOOLEAN,
          FormulaKind.OR);
    } else if (pParam1.isFormula() && pParam2.isFormula()) {
      return new DRealTerm<>(
          Dreal.or(pParam1.getFormula(), pParam2.getFormula()),
          Variable.Type.BOOLEAN,
          FormulaKind.OR);
    } else {
      throw new UnsupportedOperationException(
          "Dreal does not support to creat an Or-Formula from " + "Expressions.");
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind.FormulaType> orImpl(
      Collection<DRealTerm<?, ?>> pParams) {
    Formula result = Formula.formulaFalse();
    for (DRealTerm<?, ?> formula : pParams) {
      // Only Formulas or Variables of boolean type are accepted when creating an Or-Formula
      Preconditions.checkState(
          formula.isFormula() || (formula.isVar() && (formula.getType() == Variable.Type.BOOLEAN)));
      if (formula.isFormula()) {
        if (formula.getFormulaKind() == FormulaKind.TRUE) {
          return new DRealTerm<>(Formula.formulaTrue(), Variable.Type.BOOLEAN, FormulaKind.TRUE);
        }
        result = Dreal.or(result, formula.getFormula());
      } else if (formula.isVar() && formula.getType() == Variable.Type.BOOLEAN) {
        result = Dreal.or(result, formula.getVariable());
      } else {
        throw new IllegalArgumentException(
            "Expression or Variable of not boolean type are not "
                + "supported to create an Or-Formula.");
      }
    }
    return new DRealTerm<>(result, Variable.Type.BOOLEAN, FormulaKind.OR);
  }

  // a xor b = (not(A AND B)) AND (not(not A AND not B))
  @Override
  protected DRealTerm<Formula, FormulaKind.FormulaType> xor(
      DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isVar() && pParam2.isFormula()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(pParam1.getType() == Variable.Type.BOOLEAN);
      return new DRealTerm<>(
          Dreal.and(
              Dreal.not(Dreal.and(pParam1.getVariable(), pParam2.getFormula())),
              Dreal.not(
                  Dreal.and(Dreal.not(pParam1.getVariable()), Dreal.not(pParam2.getFormula())))),
          Variable.Type.BOOLEAN,
          FormulaKind.AND);
    } else if (pParam1.isFormula() && pParam2.isVar()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(pParam2.getType() == Variable.Type.BOOLEAN);
      return new DRealTerm<>(
          Dreal.and(
              Dreal.not(Dreal.and(pParam1.getFormula(), pParam2.getVariable())),
              Dreal.not(
                  Dreal.and(Dreal.not(pParam1.getFormula()), Dreal.not(pParam2.getVariable())))),
          Variable.Type.BOOLEAN,
          FormulaKind.AND);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(pParam1.getType() == Variable.Type.BOOLEAN);
      Preconditions.checkState(pParam2.getType() == Variable.Type.BOOLEAN);
      return new DRealTerm<>(
          Dreal.and(
              Dreal.not(Dreal.and(pParam1.getVariable(), pParam2.getVariable())),
              Dreal.not(
                  Dreal.and(Dreal.not(pParam1.getVariable()), Dreal.not(pParam2.getVariable())))),
          Variable.Type.BOOLEAN,
          FormulaKind.AND);
    } else if (pParam1.isFormula() && pParam2.isFormula()) {
      return new DRealTerm<>(
          Dreal.and(
              Dreal.not(Dreal.and(pParam1.getFormula(), pParam2.getFormula())),
              Dreal.not(
                  Dreal.and(Dreal.not(pParam1.getFormula()), Dreal.not(pParam2.getFormula())))),
          Variable.Type.BOOLEAN,
          FormulaKind.AND);
    } else {
      throw new UnsupportedOperationException(
          "Dreal does not support to create a Xor-Formula " + "from Expressions.");
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind.FormulaType> equivalence(
      DRealTerm<?, ?> bits1, DRealTerm<?, ?> bits2) {
    if (bits1.isVar() && bits2.isFormula()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(bits1.getType() == Variable.Type.BOOLEAN);
      return new DRealTerm<>(
          Dreal.iff(bits1.getVariable(), bits2.getFormula()),
          Variable.Type.BOOLEAN,
          FormulaKind.EQ);
    } else if (bits1.isFormula() && bits2.isVar()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(bits2.getType() == Variable.Type.BOOLEAN);
      return new DRealTerm<>(
          Dreal.iff(bits1.getFormula(), bits2.getVariable()),
          Variable.Type.BOOLEAN,
          FormulaKind.EQ);
    } else if (bits1.isVar() && bits2.isVar()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(bits1.getType() == Variable.Type.BOOLEAN);
      Preconditions.checkState(bits2.getType() == Variable.Type.BOOLEAN);
      return new DRealTerm<>(
          Dreal.iff(bits1.getVariable(), bits2.getVariable()),
          Variable.Type.BOOLEAN,
          FormulaKind.EQ);
    } else if (bits1.isFormula() && bits2.isFormula()) {
      return new DRealTerm<>(
          Dreal.iff(bits1.getFormula(), bits2.getFormula()), Variable.Type.BOOLEAN, FormulaKind.EQ);
    } else {
      throw new UnsupportedOperationException(
          "Dreal does not support to create an iff-Formula " + "from Expressions.");
    }
  }

  @Override
  protected boolean isTrue(DRealTerm<?, ?> bits) {
    if (bits.isFormula()) {
      return Dreal.isTrue(bits.getFormula());
    } else if (bits.isVar()) {
      if (bits.getType() == Variable.Type.BOOLEAN) {
        return Dreal.isTrue(new Formula(bits.getVariable()));
      } else {
        throw new UnsupportedOperationException(
            "Dreal does not support isTrue on Variables not being Boolean type.");
      }
    } else {
      throw new UnsupportedOperationException("Dreal does not support isTrue on Expressions.");
    }
  }

  @Override
  protected boolean isFalse(DRealTerm<?, ?> bits) {
    if (bits.isFormula()) {
      return Dreal.isFalse(bits.getFormula());
    } else if (bits.isVar()) {
      if (bits.getType() == Variable.Type.BOOLEAN) {
        return Dreal.isFalse(new Formula(bits.getVariable()));
      } else {
        throw new UnsupportedOperationException(
            "Dreal does not support isTrue on Variables not being Boolean type.");
      }
    } else {
      throw new UnsupportedOperationException("Dreal does not support isTrue on Expressions.");
    }
  }

  // Dreal only allows ITE on Formulas as condition, and else and then arguments to be
  // Expressions. But because a formula can be created from a variable of boolean type and an
  // expression can be created from a variable, there are a lot of cases that need to be
  // considered. The rest ist implemented with (!(cond) || f1) && (cond || f2) or an exception is
  // thrown if not possible
  @Override
  protected DRealTerm<?, ?> ifThenElse(
      DRealTerm<?, ?> cond, DRealTerm<?, ?> f1, DRealTerm<?, ?> f2) {
    if (f1.equals(f2)) {
      return f1;
    }
    if (cond.isVar()) {
      if (cond.getType() == Variable.Type.BOOLEAN) {
        if (f1.isExp() && f2.isExp()) {
          return new DRealTerm<>(
              Dreal.ifThenElse(
                  new Formula(cond.getVariable()), f1.getExpression(), f2.getExpression()),
              f1.getType(),
              ExpressionKind.ITE);
        } else if (f1.isVar() && f2.isExp()) {
          if (f1.getType() != Variable.Type.BOOLEAN) {
            return new DRealTerm<>(
                Dreal.ifThenElse(
                    new Formula(cond.getVariable()),
                    new Expression(f1.getVariable()),
                    f2.getExpression()),
                f1.getType(),
                ExpressionKind.ITE);
          } else {
            throw new UnsupportedOperationException(
                "Dreal does not support ITE with Variable of "
                    + "Boolean type and Expression as else and then arguments.");
          }
        } else if (f1.isExp() && f2.isVar()) {
          if (f2.getType() != Variable.Type.BOOLEAN) {
            return new DRealTerm<>(
                Dreal.ifThenElse(
                    new Formula(cond.getVariable()),
                    f1.getExpression(),
                    new Expression(f2.getVariable())),
                f1.getType(),
                ExpressionKind.ITE);
          } else {
            throw new UnsupportedOperationException(
                "Dreal does not support ITE with Variable of "
                    + "Boolean type and Expression as else and then arguments.");
          }
        } else if (f1.isVar() && f2.isVar()) {
          if (f1.getType() != Variable.Type.BOOLEAN && f2.getType() != Variable.Type.BOOLEAN) {
            return new DRealTerm<>(
                Dreal.ifThenElse(
                    new Formula(cond.getVariable()),
                    new Expression(f1.getVariable()),
                    new Expression(f2.getVariable())),
                f1.getType(),
                ExpressionKind.ITE);
          } else if (f1.getType() == Variable.Type.BOOLEAN
              && f2.getType() == Variable.Type.BOOLEAN) {
            return new DRealTerm<>(
                Dreal.and(
                    Dreal.or(
                        Dreal.not(new Formula(cond.getVariable())), new Formula(f1.getVariable())),
                    Dreal.or(new Formula(cond.getVariable()), new Formula(f2.getVariable()))),
                f1.getType(),
                FormulaKind.AND);
          } else {
            throw new UnsupportedOperationException(
                "Dreal does not support Variable of boolean "
                    + "type and Variable of different type to be else and then argumnets.");
          }
        } else if (f1.isFormula() && f2.isFormula()) {
          return new DRealTerm<>(
              Dreal.and(
                  Dreal.or(Dreal.not(new Formula(cond.getVariable())), f1.getFormula()),
                  Dreal.or(new Formula(cond.getVariable()), f2.getFormula())),
              f1.getType(),
              FormulaKind.AND);
        } else {
          throw new UnsupportedOperationException(
              "Dreal does not support Expression and Formula as then and else.");
        }
      } else {
        throw new UnsupportedOperationException(
            "Dreal does not support a Variable of not boolean type as condition.");
      }
    } else if (cond.isFormula()) {
      if (f1.isExp() && f2.isExp()) {
        return new DRealTerm<>(
            Dreal.ifThenElse(cond.getFormula(), f1.getExpression(), f2.getExpression()),
            f1.getType(),
            ExpressionKind.ITE);
      } else if (f1.isVar() && f2.isExp()) {
        if (f1.getType() != Variable.Type.BOOLEAN) {
          return new DRealTerm<>(
              Dreal.ifThenElse(
                  cond.getFormula(), new Expression(f1.getVariable()), f2.getExpression()),
              f1.getType(),
              ExpressionKind.ITE);
        } else {
          throw new UnsupportedOperationException(
              "Dreal does not support ITE with Variable of "
                  + "Boolean type and Expression as else and then arguments.");
        }
      } else if (f1.isExp() && f2.isVar()) {
        if (f2.getType() != Variable.Type.BOOLEAN) {
          return new DRealTerm<>(
              Dreal.ifThenElse(
                  cond.getFormula(), f1.getExpression(), new Expression(f2.getVariable())),
              f1.getType(),
              ExpressionKind.ITE);
        } else {
          throw new UnsupportedOperationException(
              "Dreal does not support ITE with Variable of "
                  + "Boolean type and Expression as else and then arguments.");
        }
      } else if (f1.isVar() && f2.isVar()) {
        if (f1.getType() != Variable.Type.BOOLEAN && f2.getType() == Variable.Type.BOOLEAN) {
          return new DRealTerm<>(
              Dreal.ifThenElse(
                  cond.getFormula(),
                  new Expression(f1.getVariable()),
                  new Expression(f2.getVariable())),
              f1.getType(),
              ExpressionKind.ITE);
        } else if (f1.getType() == Variable.Type.BOOLEAN && f2.getType() == Variable.Type.BOOLEAN) {
          return new DRealTerm<>(
              Dreal.and(
                  Dreal.or(Dreal.not(cond.getFormula()), new Formula(f1.getVariable())),
                  Dreal.or(cond.getFormula(), new Formula(f2.getVariable()))),
              f1.getType(),
              FormulaKind.AND);
        } else {
          throw new UnsupportedOperationException(
              "Dreal does not support Variable of boolean "
                  + "type and Variable of different type to be else and then argumnets.");
        }
      } else if (f1.isFormula() && f2.isFormula()) {
        return new DRealTerm<>(
            Dreal.and(
                Dreal.or(Dreal.not(cond.getFormula()), f1.getFormula()),
                Dreal.or(cond.getFormula(), f2.getFormula())),
            f1.getType(),
            FormulaKind.AND);
      } else {
        throw new UnsupportedOperationException(
            "Dreal does not support Expression and Formula " + "as then and else.");
      }
    } else {
      throw new UnsupportedOperationException("Dreal does not support an Expression as condition.");
    }
  }
}
