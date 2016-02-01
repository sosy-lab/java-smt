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
package org.sosy_lab.solver.z3java;

import com.microsoft.z3.Expr;

import org.sosy_lab.solver.api.ArrayFormula;
import org.sosy_lab.solver.api.BitvectorFormula;
import org.sosy_lab.solver.api.BooleanFormula;
import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.api.FormulaType;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.solver.api.NumeralFormula.RationalFormula;

import javax.annotation.Nullable;

abstract class Z3Formula implements Formula {

  private final Expr z3expr;

  private Z3Formula(Expr z3expr) {
    this.z3expr = z3expr;
  }

  @Override
  public final String toString() {
    return z3expr.toString();
  }

  @Override
  public final boolean equals(@Nullable Object obj) {
    if (obj == null || !(obj instanceof Z3Formula)) {
      return false;
    }
    Z3Formula other = (Z3Formula) obj;
    return z3expr.equals(other.z3expr);
  }

  @Override
  public final int hashCode() {
    return z3expr.hashCode();
  }

  final Expr getFormulaInfo() {
    return z3expr;
  }

  static final class Z3ArrayFormula<TI extends Formula, TE extends Formula> extends Z3Formula
      implements ArrayFormula<TI, TE> {

    private final FormulaType<TI> indexType;
    private final FormulaType<TE> elementType;

    Z3ArrayFormula(Expr pZ3expr, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
      super(pZ3expr);
      indexType = pIndexType;
      elementType = pElementType;
    }

    public FormulaType<TI> getIndexType() {
      return indexType;
    }

    public FormulaType<TE> getElementType() {
      return elementType;
    }
  }

  static final class Z3BitvectorFormula extends Z3Formula implements BitvectorFormula {

    Z3BitvectorFormula(Expr z3expr) {
      super(z3expr);
    }
  }

  static final class Z3IntegerFormula extends Z3Formula implements IntegerFormula {

    Z3IntegerFormula(Expr z3expr) {
      super(z3expr);
    }
  }

  static final class Z3RationalFormula extends Z3Formula implements RationalFormula {

    Z3RationalFormula(Expr z3expr) {
      super(z3expr);
    }
  }

  static final class Z3BooleanFormula extends Z3Formula implements BooleanFormula {
    Z3BooleanFormula(Expr z3expr) {
      super(z3expr);
    }
  }
}
