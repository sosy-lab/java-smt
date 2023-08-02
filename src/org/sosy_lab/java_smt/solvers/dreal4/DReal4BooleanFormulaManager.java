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
import java.util.Collection;
import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Context;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable.Type;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.dreal;


public class DReal4BooleanFormulaManager
    extends AbstractBooleanFormulaManager<DRealTerm<?, ?>, Type, Context, DRealTerm<?, ?>> {

  protected DReal4BooleanFormulaManager(DReal4FormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected DRealTerm<?, ?> makeVariableImpl(String pVar) {
    return formulaCreator.makeVariable(getFormulaCreator().getBoolType(), pVar);
  }

  @Override
  protected DRealTerm<Formula, FormulaKind> makeBooleanImpl(boolean value) {
    if (value) {
      return new DRealTerm<>(Formula.True(), Type.BOOLEAN, FormulaKind.True);
    } else {
      return new DRealTerm<>(Formula.False(), Type.BOOLEAN, FormulaKind.False);
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind> not(DRealTerm<?, ?> pParam1) {
    if (pParam1.isFormula()) {
      return new DRealTerm<>(dreal.Not(pParam1.getFormula()), Type.BOOLEAN,
          FormulaKind.Not);
    } else if (pParam1.isVar()) {
      Preconditions.checkState(pParam1.getVariable().get_type() == Type.BOOLEAN);
      return new DRealTerm<>(dreal.Not(new Formula(pParam1.getVariable())), Type.BOOLEAN,
          FormulaKind.Not);
    } else {
      throw new UnsupportedOperationException("dReal does not support not on Expressions.");
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind> and(DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isVar() && pParam2.isFormula()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(pParam1.getVariable().get_type() == Type.BOOLEAN);
      return new DRealTerm<>(dreal.And(pParam1.getVariable(), pParam2.getFormula()),
          Type.BOOLEAN, FormulaKind.And);
    } else if (pParam1.isFormula() && pParam2.isVar()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(pParam2.getVariable().get_type() == Type.BOOLEAN);
      return new DRealTerm<>(dreal.And(pParam1.getFormula(), pParam2.getVariable()),
          Type.BOOLEAN, FormulaKind.And);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(pParam1.getVariable().get_type() == Type.BOOLEAN);
      Preconditions.checkState(pParam2.getVariable().get_type() == Type.BOOLEAN);
      return new DRealTerm<>(dreal.And(pParam1.getVariable(), pParam2.getVariable()),
          Type.BOOLEAN, FormulaKind.And);
    } else if (pParam1.isFormula() && pParam2.isFormula()) {
      DRealTerm<?, ?> test = new DRealTerm<>(dreal.And(pParam1.getFormula(), pParam2.getFormula()),
          Type.BOOLEAN, FormulaKind.And);
      return new DRealTerm<>(dreal.And(pParam1.getFormula(), pParam2.getFormula()),
          Type.BOOLEAN, FormulaKind.And);
    } else {
      throw new UnsupportedOperationException("dReal does not support and on Expressions.");
    }
  }
  @Override
  protected DRealTerm<Formula, FormulaKind> andImpl(Collection<DRealTerm<?, ?>> pParams) {
    Formula result = Formula.True();
    for (DRealTerm<?, ?> formula : pParams) {
      if (formula.isFormula()) {
        if (formula.getFormula().get_kind() == FormulaKind.True) {
          return new DRealTerm<>(Formula.True(), Type.BOOLEAN, FormulaKind.True);
        }
        result = dreal.And(result, formula.getFormula());
      } else if (formula.isVar() && formula.getVariable().get_type() == Type.BOOLEAN) {
        result = dreal.And(result, formula.getVariable());
      } else {
        throw new IllegalArgumentException("Expression and Variable of not type boolean are not "
            + "supported to create an And-Formula.");
      }
    }
    return new DRealTerm<>(result, Type.BOOLEAN, FormulaKind.And);
  }


  @Override
  protected DRealTerm<Formula, FormulaKind> or(DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isVar() && pParam2.isFormula()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(pParam1.getVariable().get_type() == Type.BOOLEAN);
      return new DRealTerm<>(dreal.Or(pParam1.getVariable(), pParam2.getFormula()),
          Type.BOOLEAN, FormulaKind.Or);
    } else if (pParam1.isFormula() && pParam2.isVar()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(pParam2.getVariable().get_type() == Type.BOOLEAN);
      return new DRealTerm<>(dreal.Or(pParam1.getFormula(), pParam2.getVariable()),
          Type.BOOLEAN, FormulaKind.Or);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(pParam1.getVariable().get_type() == Type.BOOLEAN);
      Preconditions.checkState(pParam2.getVariable().get_type() == Type.BOOLEAN);
      return new DRealTerm<>(dreal.Or(pParam1.getVariable(), pParam2.getVariable()),
          Type.BOOLEAN, FormulaKind.Or);
    } else if (pParam1.isFormula() && pParam2.isFormula()) {
      return new DRealTerm<>(dreal.Or(pParam1.getFormula(), pParam2.getFormula()),
          Type.BOOLEAN, FormulaKind.Or);
    } else {
      throw new UnsupportedOperationException("dReal does not support or on Expressions.");
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind> orImpl(Collection<DRealTerm<?, ?>> pParams) {
    Formula result = Formula.False();
    for (DRealTerm<?, ?> formula : pParams) {
      // Only Formulas or Variables of boolean type are accepted when creating an Or-Formula
      Preconditions.checkState(formula.isFormula() || (formula.isVar()) && (formula.getVariable().get_type() == Type.BOOLEAN));
      if (formula.isFormula()) {
        if (formula.getFormula().get_kind() == FormulaKind.True) {
          return new DRealTerm<>(Formula.True(), Type.BOOLEAN, FormulaKind.True);
        }
        result = dreal.Or(result, formula.getFormula());
      } else if (formula.isVar() && formula.getVariable().get_type() == Type.BOOLEAN) {
        result = dreal.Or(result, formula.getVariable());
      }
    }
    return new DRealTerm<>(result, Type.BOOLEAN, FormulaKind.Or);
  }

  // a xor b = (NOT(A AND B)) AND (NOT(NOT A AND NOT B))
  @Override
  protected DRealTerm<Formula, FormulaKind> xor(DRealTerm<?, ?> pParam1, DRealTerm<?, ?> pParam2) {
    if (pParam1.isVar() && pParam2.isFormula()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(pParam1.getVariable().get_type() == Type.BOOLEAN);
      return new DRealTerm<>(dreal.And(dreal.Not(dreal.And(pParam1.getVariable(),
              pParam2.getFormula())),
          dreal.Not(dreal.And(dreal.Not(pParam1.getVariable()),
              dreal.Not(pParam2.getFormula())))), Type.BOOLEAN, FormulaKind.And);
    } else if (pParam1.isFormula() && pParam2.isVar()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(pParam2.getVariable().get_type() == Type.BOOLEAN);
      return new DRealTerm<>(dreal.And(dreal.Not(dreal.And(pParam1.getFormula(),
              pParam2.getVariable())),
          dreal.Not(dreal.And(dreal.Not(pParam1.getFormula()),
              dreal.Not(pParam2.getVariable())))), Type.BOOLEAN, FormulaKind.And);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(pParam1.getVariable().get_type() == Type.BOOLEAN);
      Preconditions.checkState(pParam2.getVariable().get_type() == Type.BOOLEAN);
      return new DRealTerm<>(dreal.And(dreal.Not(dreal.And(pParam1.getVariable(),
              pParam2.getVariable())),
          dreal.Not(dreal.And(dreal.Not(pParam1.getVariable()),
              dreal.Not(pParam2.getVariable())))), Type.BOOLEAN, FormulaKind.And);
    } else if (pParam1.isFormula() && pParam2.isFormula()) {
      return new DRealTerm<>(dreal.And(dreal.Not(dreal.And(pParam1.getFormula(),
              pParam2.getFormula())),
          dreal.Not(dreal.And(dreal.Not(pParam1.getFormula()),
              dreal.Not(pParam2.getFormula())))), Type.BOOLEAN, FormulaKind.And);
    } else {
      throw new UnsupportedOperationException("dReal does not support xor on Expressions.");
    }
  }

  @Override
  protected DRealTerm<Formula, FormulaKind> equivalence(DRealTerm<?, ?> bits1,
                                                        DRealTerm<?, ?> bits2) {
    if (bits1.isVar() && bits2.isFormula()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(bits1.getVariable().get_type() == Type.BOOLEAN);
      return new DRealTerm<>(dreal.iff(bits1.getVariable(), bits2.getFormula()),
          Type.BOOLEAN, FormulaKind.And);
    } else if (bits1.isFormula() && bits2.isVar()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(bits2.getVariable().get_type() == Type.BOOLEAN);
      return new DRealTerm<>(dreal.iff(bits1.getFormula(), bits2.getVariable()),
          Type.BOOLEAN, FormulaKind.And);
    } else if (bits1.isVar() && bits2.isVar()) {
      // Only Variables with type boolean are allowed
      Preconditions.checkState(bits1.getVariable().get_type() == Type.BOOLEAN);
      Preconditions.checkState(bits2.getVariable().get_type() == Type.BOOLEAN);
      return new DRealTerm<>(dreal.iff(bits1.getVariable(), bits2.getVariable()),
          Type.BOOLEAN, FormulaKind.And);
    } else if (bits1.isFormula() && bits2.isFormula()) {
      return new DRealTerm<>(dreal.iff(bits1.getFormula(), bits2.getFormula()),
          Type.BOOLEAN, FormulaKind.And);
    } else {
      throw new UnsupportedOperationException("dReal does not support iff on Expressions.");
    }
  }

  @Override
  protected boolean isTrue(DRealTerm<?, ?> bits) {
    if (bits.isFormula()) {
      return dreal.is_true(bits.getFormula());
    } else {
      throw new UnsupportedOperationException("dReal does not support isTrue on "
          + "Variables and Expressions.");
    }
  }

  @Override
  protected boolean isFalse(DRealTerm<?, ?> bits) {
    if (bits.isFormula()) {
      return dreal.is_false(bits.getFormula());
    } else {
      throw new UnsupportedOperationException("dReal does not support isTrue on "
          + "Variables and Expressions.");
    }
  }

  @Override
  protected DRealTerm<?, ?> ifThenElse(DRealTerm<?, ?> cond, DRealTerm<?, ?> f1,
                                                       DRealTerm<?, ?> f2) {
    if (cond.isFormula()) {
      if (dreal.is_true(cond.getFormula())) {
        if (f1.isVar()) {
          return new DRealTerm<>(f1.getVariable(), f1.getType(),
              f1.getType());
        } else if (f1.isExp()) {
          return new DRealTerm<>(f1.getExpression(), f1.getType(),
              f1.getExpressionKind());
        } else {
          return new DRealTerm<>(f1.getFormula(), f1.getType(),
              f1.getFormulaKind());
        }
      } else {
        if (f2.isVar()) {
          return new DRealTerm<>(f2.getVariable(), f2.getType(),
             f2.getType());
        } else if (f2.isExp()) {
          return new DRealTerm<>(f2.getExpression(), f2.getType(),
              f2.getExpressionKind());
        } else {
          return new DRealTerm<>(f2.getFormula(), f2.getType(),
              f2.getFormulaKind());
        }
      }
    } else {
      throw new UnsupportedOperationException("dReal does not suppord ifThenElse with first "
          + "argument beeing not a Formula.");
    }
  }

}