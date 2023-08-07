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
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaKind;

abstract class DReal4Formula implements Formula {

  private final DRealTerm<?, ?> term;

  DReal4Formula(DRealTerm<?, ?> pTerm) {
    this.term = pTerm;
  }

  final DRealTerm<?, ?> getTerm() {
    return term;
  }

  @Override
  public final boolean equals(Object o) {
    if ( o == this) {
      return true;
    }
    if (!(o instanceof DReal4Formula)) {
      return false;
    }
    // equal_to only checks for the same structure
    DRealTerm<?, ?> oTerm = ((DReal4Formula) o).getTerm();
    if (term.isVar() && oTerm.isVar()) {
      return term.getVariable().equal_to(oTerm.getVariable());
    } else if (term.isExp() && oTerm.isExp()) {
      return term.getExpression().EqualTo(oTerm.getExpression());
    } else if (term.isFormula() && oTerm.isFormula()) {
      return term.getFormula().EqualTo(oTerm.getFormula());
    } else {
      return false;
    }
  }

  @Override
  public final String toString() {
    if (term.isExp()) {
      return term.getExpression().to_string();
    } else if (term.isFormula()){
      return term.getFormula().to_string();
    } else {
      return term.getVariable().to_string();
    }
  }

  @Override
  public final int hashCode() {
    if (term.isExp()) {
      return (int) term.getExpression().get_hash();
    } else if (term.isFormula()){
      return (int) term.getFormula().get_hash();
    } else {
      return (int) term.getVariable().get_hash();
    }
  }

  static final class DReal4BooleanFormula extends DReal4Formula implements BooleanFormula {
    DReal4BooleanFormula(DRealTerm<?, ?> pTerm) {
      super(pTerm);
    }
  }

  static final class DReal4RationalFormula extends DReal4Formula implements RationalFormula {
    DReal4RationalFormula(DRealTerm<?, ?> pTerm) {
      super(pTerm);
    }
  }

  static final class DReal4IntegerFormula extends DReal4Formula implements IntegerFormula {
    DReal4IntegerFormula(DRealTerm<?, ?> pTerm) {
      super(pTerm);
    }
  }

}
