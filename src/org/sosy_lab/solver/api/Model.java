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
package org.sosy_lab.solver.api;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;

import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.solver.api.Model.ValueAssignment;
import org.sosy_lab.solver.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.solver.api.NumeralFormula.RationalFormula;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Iterator;
import java.util.Objects;

import javax.annotation.Nullable;

/**
 * A model returned from the satisfiable solver environment.
 */
public interface Model extends Iterable<ValueAssignment>, AutoCloseable {

  /**
   * Evaluate a given formula substituting the values from the model.
   * Can be absent if the value is not relevant to the satisfiability
   * result.
   *
   * @param f Input formula
   * @return Either of:
   *    - Number (Rational/Double/BigInteger/Long/Integer)
   *    - Boolean
   * @throws IllegalArgumentException if a formula has unexpected type, e.g Array.
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
   * Note that iterating multiple times may be inefficient for some solvers, it is recommended
   * to use {@link BasicProverEnvironment#getModelAssignments()} instead in this case.
   */
  @Override
  Iterator<ValueAssignment> iterator();

  /**
   * Pretty-printing of the model values.
   */
  @Override
  String toString();

  /**
   * Free resources associated with this model
   * (existing {@link ValueAssignment} instances stay valid,
   * but {@link #evaluate(Formula)} etc. and {@link #iterator()} must not be called again).
   */
  @Override
  void close();

  final class ValueAssignment {

    /** the key should be of simple formula-type (Boolean/Integer/Rational/BitVector). */
    private final Formula key;

    /** the key should be boolean or numeral (Rational/Double/BigInteger/Long/Integer). */
    private final Object value;

    /** arguments can have any type.
     * We would prefer numerals (like value), but we also allow Formulas. */
    private final ImmutableList<Object> argumentsInterpretation;

    /** The name should be a 'useful' identifier for the current assignment, without parameters. */
    private final String name;

    public ValueAssignment(
        Formula key, String name, Object value, Collection<?> argumentInterpretation) {

      this.key = Preconditions.checkNotNull(key);
      this.name = Preconditions.checkNotNull(name);
      this.value = Preconditions.checkNotNull(value);
      this.argumentsInterpretation = ImmutableList.copyOf(argumentInterpretation);
    }

    /**
     * The formula AST which is assigned a given value.
     */
    public Formula getKey() {
      return key;
    }

    /**
     * Variable name for variables, function name for UFs, and array name for
     * arrays.
     */
    public String getName() {
      return name;
    }

    /**
     * Value: see the {@link #evaluate} methods for the possible types.
     */
    public Object getValue() {
      return value;
    }

    /**
     * Interpretation assigned for function arguments.
     * Empty for variables.
     */
    public ImmutableList<Object> getArgumentsInterpretation() {
      return argumentsInterpretation;
    }

    public boolean isFunction() {
      return !argumentsInterpretation.isEmpty();
    }

    public int getArity() {
      return argumentsInterpretation.size();
    }

    public Object getArgInterpretation(int i) {
      assert i < getArity();
      return argumentsInterpretation.get(i);
    }

    @Override
    public String toString() {
      StringBuilder sb = new StringBuilder().append(name);
      if (!argumentsInterpretation.isEmpty()) {
        sb.append("(");
        Joiner.on(", ").appendTo(sb, argumentsInterpretation);
        sb.append(")");
      }
      return sb.append(": ").append(value).toString();
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

      // "Key" is purposefully not included in the comparison,
      // name and arguments should be sufficient.
      boolean out =
          name.equals(other.name)
              && value.equals(other.value)
              && argumentsInterpretation.equals(other.argumentsInterpretation);
      return out;
    }

    @Override
    public int hashCode() {
      return Objects.hash(name, argumentsInterpretation, value);
    }
  }
}
