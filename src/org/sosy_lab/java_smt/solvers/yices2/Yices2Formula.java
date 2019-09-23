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
package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_term_to_string;

import com.google.errorprone.annotations.Immutable;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;

@Immutable
abstract class Yices2Formula implements Formula {

  private final int yicesTerm;

  Yices2Formula(int term) {
    this.yicesTerm = term;
  }

  @Override
  public final int hashCode() {
    return yicesTerm;
  }

  final int getTerm() {
    return yicesTerm;
  }

  @Override
  public final String toString() {
    return yices_term_to_string(yicesTerm, Integer.MAX_VALUE, 1, 0);
  }

  @Override
  public final boolean equals(Object o) {
    if (o == this) {
      return true;
    }
    if (!(o instanceof Yices2Formula)) {
      return false;
    }
    return yicesTerm == ((Yices2Formula) o).yicesTerm;
  }

  @Immutable
  static final class Yices2BitvectorFormula extends Yices2Formula implements BitvectorFormula {
    Yices2BitvectorFormula(int pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class Yices2IntegerFormula extends Yices2Formula implements IntegerFormula {
    Yices2IntegerFormula(int pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class Yices2RationalFormula extends Yices2Formula implements RationalFormula {
    Yices2RationalFormula(int pTerm) {
      super(pTerm);
    }
  }

  @Immutable
  static final class Yices2BooleanFormula extends Yices2Formula implements BooleanFormula {
    Yices2BooleanFormula(int pTerm) {
      super(pTerm);
    }
  }
}
