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
package org.sosy_lab.java_smt.solvers.boolector;

import com.google.errorprone.annotations.Immutable;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;

@Immutable
abstract class BoolectorFormula implements Formula {

  private final long btorTerm;
  private final long btor; // We need the boolector instance to calculate the hash

  BoolectorFormula(long term, long btor) {
    this.btorTerm = term;
    this.btor = btor;
  }

  final long getTerm() {
    return btorTerm;
  }

  @Override
  public final boolean equals(Object o) {
    if (o == this) {
      return true;
    }
    if (!(o instanceof BoolectorFormula)) {
      return false;
    }
    BoolectorFormula other = (BoolectorFormula) o;
    return btor == other.btor && btorTerm == other.btorTerm;
  }

  @Override
  public final int hashCode() {
    // Boolector uses structural hashing on its nodes (formulas)
    return BtorJNI.boolector_get_node_id(btor, btorTerm);
  }

  @Immutable
  static final class BoolectorBitvectorFormula extends BoolectorFormula
      implements BitvectorFormula {
    BoolectorBitvectorFormula(long pTerm, long btor) {
      super(pTerm, btor);
    }
  }

  @Immutable
  static final class BoolectorBooleanFormula extends BoolectorFormula implements BooleanFormula {
    BoolectorBooleanFormula(long pTerm, long btor) {
      super(pTerm, btor);
    }
  }

  static final class BoolectorArrayFormula<TI extends Formula, TE extends Formula>
      extends BoolectorFormula implements ArrayFormula<TI, TE> {

    private final FormulaType<TI> indexType;
    private final FormulaType<TE> elementType;

    BoolectorArrayFormula(
        long pTerm, FormulaType<TI> pIndexType, FormulaType<TE> pElementType, long btor) {
      super(pTerm, btor);
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
}
