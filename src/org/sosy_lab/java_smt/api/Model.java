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
package org.sosy_lab.java_smt.api;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.math.BigInteger;
import java.util.Collection;
import java.util.Iterator;
import java.util.Objects;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;

/** A model returned from the satisfiable solver environment. */
public interface Model extends Iterable<ValueAssignment>, AutoCloseable {

  /**
   * Evaluate a given formula substituting the values from the model and return it as formula.
   *
   * <p>If a value is not relevant to the satisfiability result, the solver can choose either to
   * insert an arbitrary value (e.g., the value <code>0</code> for the matching type) or just return
   * <code>null</code>.
   *
   * <p>The formula does not need to be a variable, we also allow complex expression. The solver
   * will replace all symbols from the formula with their model values and then simplify the formula
   * into a simple formula, e.g., consisting only of a numeral expression.
   *
   * @param formula Input formula to be evaluated.
   * @return evaluation of the given formula or <code>null</code> if the solver does not provide a
   *     better evaluation.
   */
  @Nullable
  <T extends Formula> T eval(T formula);

  /**
   * Evaluate a given formula substituting the values from the model.
   *
   * <p>If a value is not relevant to the satisfiability result, the model can choose either an
   * arbitrary value (e.g., the value <code>0</code> for the matching type) or just return <code>
   * null</code>.
   *
   * <p>The formula does not need to be a variable, we also allow complex expression.
   *
   * @param f Input formula
   * @return Either of: - Number (Rational/Double/BigInteger/Long/Integer) - Boolean
   * @throws IllegalArgumentException if a formula has unexpected type, e.g Array.
   */
  @Nullable
  Object evaluate(Formula f);

  /**
   * Type-safe evaluation for integer formulas.
   *
   * <p>The formula does not need to be a variable, we also allow complex expression.
   */
  @Nullable
  BigInteger evaluate(IntegerFormula f);

  /**
   * Type-safe evaluation for rational formulas.
   *
   * <p>The formula does not need to be a variable, we also allow complex expression.
   */
  @Nullable
  Rational evaluate(RationalFormula f);

  /**
   * Type-safe evaluation for boolean formulas.
   *
   * <p>The formula does not need to be a variable, we also allow complex expression.
   */
  @Nullable
  Boolean evaluate(BooleanFormula f);

  /**
   * Type-safe evaluation for bitvector formulas.
   *
   * <p>The formula does not need to be a variable, we also allow complex expression.
   */
  @Nullable
  BigInteger evaluate(BitvectorFormula f);

  /**
   * Iterate over all values present in the model. Note that iterating multiple times may be
   * inefficient for some solvers, it is recommended to use {@link
   * BasicProverEnvironment#getModelAssignments()} instead in this case.
   */
  @Override
  default Iterator<ValueAssignment> iterator() {
    return asList().iterator();
  }

  /** Build a list of assignments that stays valid after closing the model. */
  ImmutableList<ValueAssignment> asList();

  /** Pretty-printing of the model values. */
  @Override
  String toString();

  /**
   * Free resources associated with this model (existing {@link ValueAssignment} instances stay
   * valid, but {@link #evaluate(Formula)} etc. and {@link #iterator()} must not be called again).
   */
  @Override
  void close();

  final class ValueAssignment {

    /**
     * the key should be of simple formula-type (Boolean/Integer/Rational/BitVector).
     *
     * <p>For UFs we use the application of the UF with arguments.
     *
     * <p>For arrays we use the selection-statement with an index.
     */
    private final Formula keyFormula;

    /** the value should be of simple formula-type (Boolean/Integer/Rational/BitVector). */
    private final Formula valueFormula;

    /** the equality of key and value. */
    private final BooleanFormula formula;

    /** the key should be boolean or numeral (Rational/Double/BigInteger/Long/Integer). */
    private final Object value;

    /**
     * arguments can have any type. We would prefer numerals (like value), but we also allow
     * Formulas.
     *
     * <p>For UFs we use the arguments.
     *
     * <p>For arrays we use the index of a selection or an empty list for wildcard-selection, if the
     * whole array is filled with a constant value. In the latter case any additionally given
     * array-assignment overrides the wildcard-selection for the given index. Example: "arr=0,
     * arr[2]=3" corresponds to an array {0,0,3,0,...}.
     */
    private final ImmutableList<Object> argumentsInterpretation;

    /**
     * The name should be a 'useful' identifier for the current assignment.
     *
     * <p>For UFs we use their name without parameters.
     *
     * <p>For arrays we use the name without any index.
     */
    private final String name;

    public ValueAssignment(
        Formula keyFormula,
        Formula valueFormula,
        BooleanFormula formula,
        String name,
        Object value,
        Collection<?> argumentInterpretation) {

      this.keyFormula = Preconditions.checkNotNull(keyFormula);
      this.valueFormula = Preconditions.checkNotNull(valueFormula);
      this.formula = Preconditions.checkNotNull(formula);
      this.name = Preconditions.checkNotNull(name);
      this.value = Preconditions.checkNotNull(value);
      this.argumentsInterpretation = ImmutableList.copyOf(argumentInterpretation);
    }

    /** The formula AST which is assigned a given value. */
    public Formula getKey() {
      return keyFormula;
    }

    /** The formula AST which is assigned to a given key. */
    public Formula getValueAsFormula() {
      return valueFormula;
    }

    /** The formula AST representing the equality of key and value. */
    public BooleanFormula getAssignmentAsFormula() {
      return formula;
    }

    /** Variable name for variables, function name for UFs, and array name for arrays. */
    public String getName() {
      return name;
    }

    /** Value: see the {@link #evaluate} methods for the possible types. */
    public Object getValue() {
      return value;
    }

    /** Interpretation assigned for function arguments. Empty for variables. */
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
        sb.append('(');
        Joiner.on(", ").appendTo(sb, argumentsInterpretation);
        sb.append(')');
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
      return name.equals(other.name)
          && value.equals(other.value)
          && argumentsInterpretation.equals(other.argumentsInterpretation);
    }

    @Override
    public int hashCode() {
      return Objects.hash(name, argumentsInterpretation, value);
    }
  }
}
