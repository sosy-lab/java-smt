/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.stp;

import com.google.errorprone.annotations.Immutable;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;

@Immutable
public abstract class StpFormula implements Formula {

  private final Expr stpTerm;

  StpFormula(Expr term) {
    this.stpTerm = term;
  }

  @Override
  public final String toString() {
    return StpJavaApi.exprString(stpTerm);
  }

  @Override
  public final boolean equals(Object o) {
    if (o == this) {
      return true;
    }
    if (!(o instanceof StpFormula)) {
      return false;
    }
    return stpTerm == ((StpFormula) o).stpTerm;
  }

  @Override
  public final int hashCode() {
    return (int) Expr.getCPtr(stpTerm);
  }

  final Expr getTerm() {
    return stpTerm;
  }

  @Immutable
  static final class StpArrayFormula<TI extends Formula, TE extends Formula> extends StpFormula
      implements ArrayFormula<TI, TE> {

    private final FormulaType<TI> indexType;
    private final FormulaType<TE> elementType;

    StpArrayFormula(Expr pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
      super(pTerm);
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

  @Immutable
  static final class StpBitvectorFormula extends StpFormula implements BitvectorFormula {
    StpBitvectorFormula(Expr pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class StpBooleanFormula extends StpFormula implements BooleanFormula {
    StpBooleanFormula(Expr pTerm) {
      super(pTerm);
    }
  }
}
