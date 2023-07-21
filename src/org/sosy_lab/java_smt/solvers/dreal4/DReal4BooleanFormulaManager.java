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

import org.sosy_lab.java_smt.basicimpl.AbstractBooleanFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Context;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable.Type;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.dreal;


public class DReal4BooleanFormulaManager
    extends AbstractBooleanFormulaManager<DRealTerm, Type, Context, DRealTerm> {

  protected DReal4BooleanFormulaManager(FormulaCreator pCreator) {
    super(pCreator);
  }

  @Override
  protected DRealTerm makeVariableImpl(String pVar) {
    return formulaCreator.makeVariable(getFormulaCreator().getBoolType(), pVar);
  }

  @Override
  protected DRealTerm makeBooleanImpl(boolean value) {
    if (value) {
      return new DRealTerm(null, null, Formula.True(), Type.BOOLEAN);
    } else {
      return new DRealTerm(null, null, Formula.False(), Type.BOOLEAN);
    }
  }

  @Override
  protected DRealTerm not(DRealTerm pParam1) {
    if (pParam1.isFormula()) {
      return new DRealTerm(null, null, dreal.Not(pParam1.getFormula()), Type.BOOLEAN);
    } else {
      throw new UnsupportedOperationException("dReal does not support not on Variabele "
          + "or Expressions.");
    }
  }

  @Override
  protected DRealTerm and(DRealTerm pParam1, DRealTerm pParam2) {
    if (pParam1.isVar() && pParam2.isFormula()) {
      return new DRealTerm(null, null, dreal.And(pParam1.getVariable(), pParam2.getFormula()), Type.BOOLEAN);
    } else if (pParam1.isFormula() && pParam2.isVar()) {
      return new DRealTerm(null, null, dreal.And(pParam1.getFormula(), pParam2.getVariable()), Type.BOOLEAN);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm(null, null, dreal.And(pParam1.getVariable(), pParam2.getVariable()), Type.BOOLEAN);
    } else if (pParam1.isFormula() && pParam2.isFormula()) {
      return new DRealTerm(null, null, dreal.And(pParam1.getFormula(), pParam2.getFormula()), Type.BOOLEAN);
    } else {
      throw new UnsupportedOperationException("dReal does not support and on Expressions.");
    }
  }

  @Override
  protected DRealTerm or(DRealTerm pParam1, DRealTerm pParam2) {
    if (pParam1.isVar() && pParam2.isFormula()) {
      return new DRealTerm(null, null, dreal.Or(pParam1.getVariable(), pParam2.getFormula()), Type.BOOLEAN);
    } else if (pParam1.isFormula() && pParam2.isVar()) {
      return new DRealTerm(null, null, dreal.Or(pParam1.getFormula(), pParam2.getVariable()), Type.BOOLEAN);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm(null, null, dreal.Or(pParam1.getVariable(), pParam2.getVariable()), Type.BOOLEAN);
    } else if (pParam1.isFormula() && pParam2.isFormula()) {
      return new DRealTerm(null, null, dreal.Or(pParam1.getFormula(), pParam2.getFormula()), Type.BOOLEAN);
    } else {
      throw new UnsupportedOperationException("dReal does not support or on Expressions.");
    }
  }

  // a xor b = (NOT(A AND B)) AND (NOT(NOT A AND NOT B))
  @Override
  protected DRealTerm xor(DRealTerm pParam1, DRealTerm pParam2) {
    if (pParam1.isVar() && pParam2.isFormula()) {
      return new DRealTerm(null, null, dreal.And(dreal.Not(dreal.And(pParam1.getVariable(),
              pParam2.getFormula())),
          dreal.Not(dreal.And(dreal.Not(pParam1.getVariable()),
              dreal.Not(pParam2.getFormula())))), Type.BOOLEAN);
    } else if (pParam1.isFormula() && pParam2.isVar()) {
      return new DRealTerm(null, null, dreal.And(dreal.Not(dreal.And(pParam1.getFormula(),
              pParam2.getVariable())),
          dreal.Not(dreal.And(dreal.Not(pParam1.getFormula()),
              dreal.Not(pParam2.getVariable())))), Type.BOOLEAN);
    } else if (pParam1.isVar() && pParam2.isVar()) {
      return new DRealTerm(null, null, dreal.And(dreal.Not(dreal.And(pParam1.getVariable(),
              pParam2.getVariable())),
          dreal.Not(dreal.And(dreal.Not(pParam1.getVariable()),
              dreal.Not(pParam2.getVariable())))), Type.BOOLEAN);
    } else if (pParam1.isFormula() && pParam2.isFormula()) {
      return new DRealTerm(null, null, dreal.And(dreal.Not(dreal.And(pParam1.getFormula(),
              pParam2.getFormula())),
          dreal.Not(dreal.And(dreal.Not(pParam1.getFormula()),
              dreal.Not(pParam2.getFormula())))), Type.BOOLEAN);
    } else {
      throw new UnsupportedOperationException("dReal does not support xor on Expressions.");
    }
  }

  @Override
  protected DRealTerm equivalence(DRealTerm bits1, DRealTerm bits2) {
    if (bits1.isVar() && bits2.isFormula()) {
      return new DRealTerm(null, null, dreal.iff(bits1.getVariable(), bits2.getFormula()), Type.BOOLEAN);
    } else if (bits1.isFormula() && bits2.isVar()) {
      return new DRealTerm(null, null, dreal.iff(bits1.getFormula(), bits2.getVariable()), Type.BOOLEAN);
    } else if (bits1.isVar() && bits2.isVar()) {
      return new DRealTerm(null, null, dreal.iff(bits1.getVariable(), bits2.getVariable()), Type.BOOLEAN);
    } else if (bits1.isFormula() && bits2.isFormula()) {
      return new DRealTerm(null, null, dreal.iff(bits1.getFormula(), bits2.getFormula()), Type.BOOLEAN);
    } else {
      throw new UnsupportedOperationException("dReal does not support iff on Expressions.");
    }
  }

  @Override
  protected boolean isTrue(DRealTerm bits) {
    if (bits.isFormula()) {
      return dreal.is_true(bits.getFormula());
    } else {
      throw new UnsupportedOperationException("dReal does not support isTrue on "
          + "Variables and Expressions.");
    }
  }

  @Override
  protected boolean isFalse(DRealTerm bits) {
    if (bits.isFormula()) {
      return dreal.is_false(bits.getFormula());
    } else {
      throw new UnsupportedOperationException("dReal does not support isTrue on "
          + "Variables and Expressions.");
    }
  }

  @Override
  protected DRealTerm ifThenElse(DRealTerm cond, DRealTerm f1, DRealTerm f2) {
    if (cond.isFormula()) {
      if (dreal.is_true(cond.getFormula())) {
        if (f1.isVar()) {
          return new DRealTerm(f1.getVariable(), null, null, Type.BOOLEAN);
        } else if (f1.isExp()) {
          return new DRealTerm(null, f1.getExpression(), null, Type.BOOLEAN);
        } else {
          return new DRealTerm(null, null, f1.getFormula(), Type.BOOLEAN);
        }
      } else {
        if (f2.isVar()) {
          return new DRealTerm(f2.getVariable(), null, null, Type.BOOLEAN);
        } else if (f2.isExp()) {
          return new DRealTerm(null, f2.getExpression(), null, Type.BOOLEAN);
        } else {
          return new DRealTerm(null, null, f2.getFormula(), Type.BOOLEAN);
        }
      }
    } else {
      throw new UnsupportedOperationException("dReal does not suppord ifThenElse with first "
          + "argument beeing not a Formula.");
    }
  }

}