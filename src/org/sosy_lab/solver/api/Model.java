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
package org.sosy_lab.solver.api;

import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.solver.api.Model.ValueAssignment;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.solver.api.NumeralFormula.RationalFormula;

import java.math.BigInteger;
import java.util.Iterator;
import java.util.Objects;

import javax.annotation.Nullable;

/**
 * A model returned from the satisfiable solver environment.
 */
public interface Model extends Iterable<ValueAssignment> {

  /**
   * Evaluate a given formula substituting the values from the model.
   * Can be absent if the value is not relevant to the satisfiability
   * result.
   *
   * @param f Input formula
   * @return Either of:
   *    - Number (Rational/Double/BigInteger/Long/Integer)
   *    - Boolean
   *    - String (for types we do not handle)
   */
  @Nullable
  Object evaluate(Formula f);

  /**
   * Type-safe evaluation for integer formulas.
   */
  @Nullable
  BigInteger evaluate(IntegerFormula f);

  /**
   * Type-safe evaluation for rational formulas.
   */
  @Nullable
  Rational evaluate(RationalFormula f);

  /**
   * Type-safe evaluation for boolean formulas.
   */
  @Nullable
  Boolean evaluate(BooleanFormula f);

  /**
   * Type-safe evaluation for bitvector formulas.
   */
  @Nullable
  BigInteger evaluate(BitvectorFormula f);

  /**
   * Iterate over all values present in the model.
   */
  @Override
  Iterator<ValueAssignment> iterator();

  /**
   * Pretty-printing of the model values.
   */
  @Override
  String toString();

  final class ValueAssignment {
    final Formula key;
    final Object value;

    public ValueAssignment(Formula key, Object value) {
      this.key = key;
      this.value = value;
    }

    public Formula getKey() {
      return key;
    }

    public Object getValue() {
      return value;
    }

    @Override
    public String toString() {
      return String.format("%s=%s", key, value);
    }

    @Override
    public boolean equals(Object o) {
      if (o == this) {
        return true;
      }
      if (!(o instanceof ValueAssignment)) {
        return false;
      }
      ValueAssignment other = (ValueAssignment) o;
      return key.equals(other.key) && value.equals(other.value);
    }

    @Override
    public int hashCode() {
      return Objects.hash(key, value);
    }
  }
}
