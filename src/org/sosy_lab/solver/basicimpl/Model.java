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
package org.sosy_lab.solver.basicimpl;

import com.google.common.base.Optional;

import org.sosy_lab.solver.api.Formula;
import org.sosy_lab.solver.basicimpl.Model.ValueAssignment;

import java.util.Iterator;
import java.util.Objects;

public interface Model extends Iterable<ValueAssignment> {

  /**
   * Evaluate a given formula substituting the values from the model.
   * Can be absent if the value is not relevant to the satisfiability
   * result.
   *
   * @param f Input formula
   * @return Either of:
   *    - Number
   *    - Boolean
   */
  Optional<Object> evaluate(Formula f);

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
