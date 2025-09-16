// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_model;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_model_iterator;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_is_array_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_array_read;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_make_eq;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_model_create_iterator;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_model_eval;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_model_iterator_has_next;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_model_iterator_next;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_arity;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_get_arg;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_get_type;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_term_is_array_write;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Set;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;

class Mathsat5Model extends AbstractModel<Long, Long, Long> {

  private final long model;
  private final Mathsat5FormulaCreator formulaCreator;

  /** for detecting closed environments, Exception is better than SegFault. */
  private final Mathsat5AbstractProver<?> prover;

  Mathsat5Model(
      FormulaManager pFormulaManager,
      long model,
      Mathsat5FormulaCreator creator,
      Mathsat5AbstractProver<?> pProver) {
    super(pFormulaManager, pProver, creator);
    this.model = model;
    formulaCreator = creator;
    prover = pProver;
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    Preconditions.checkState(!isClosed());
    Preconditions.checkState(!prover.isClosed(), "cannot use model after prover is closed");
    ImmutableList.Builder<ValueAssignment> assignments = ImmutableList.builder();

    long modelIterator = msat_model_create_iterator(model);
    while (msat_model_iterator_has_next(modelIterator)) {
      long[] key = new long[1];
      long[] value = new long[1];
      if (msat_model_iterator_next(modelIterator, key, value)) {
        throw new NoSuchElementException();
      }

      if (msat_is_array_type(creator.getEnv(), msat_term_get_type(value[0]))) {
        assignments.addAll(getArrayAssignments(key[0], key[0], value[0], ImmutableList.of()));
      } else {
        assignments.add(getAssignment(key[0], value[0]));
      }
    }
    msat_destroy_model_iterator(modelIterator);
    return assignments.build();
  }

  private ValueAssignment getAssignment(long key, long value) {
    List<Object> argumentInterpretation = new ArrayList<>();
    for (int i = 0; i < msat_term_arity(key); i++) {
      long arg = msat_term_get_arg(key, i);
      argumentInterpretation.add(evaluateImpl(arg));
    }

    return new ValueAssignment(
        creator.encapsulateWithTypeOf(key),
        creator.encapsulateWithTypeOf(value),
        creator.encapsulateBoolean(msat_make_eq(creator.getEnv(), key, value)),
        formulaCreator.getName(key),
        formulaCreator.convertValue(key, value),
        argumentInterpretation);
  }

  /** split an array-assignment into several assignments for all positions. */
  private Collection<ValueAssignment> getArrayAssignments(
      long symbol, long key, long array, List<Object> upperIndices) {
    Collection<ValueAssignment> assignments = new ArrayList<>();
    Set<Long> indices = new HashSet<>();
    while (msat_term_is_array_write(creator.getEnv(), array)) {
      long index = msat_term_get_arg(array, 1);
      long content = msat_term_get_arg(array, 2);
      array = msat_term_get_arg(array, 0);

      if (!indices.add(index)) {
        // sometimes MathSat5 provides a model-assignment like
        // "ARR := (write (write (write (const 0) 5 1) 0 0) 5 2)",
        // where the index "5" is assigned twice, even with different values.
        // In this case we skip the second (deeper nested) assignment.
        // In this example we ignore the assignment "ARR[5] := 1".
        continue;
      }

      List<Object> innerIndices = new ArrayList<>(upperIndices);
      innerIndices.add(evaluateImpl(index));
      long select = msat_make_array_read(creator.getEnv(), key, index);
      if (msat_is_array_type(creator.getEnv(), msat_term_get_type(content))) {
        assignments.addAll(getArrayAssignments(symbol, select, content, innerIndices));
      } else {
        assignments.add(
            new ValueAssignment(
                creator.encapsulateWithTypeOf(select),
                creator.encapsulateWithTypeOf(content),
                creator.encapsulateBoolean(msat_make_eq(creator.getEnv(), select, content)),
                formulaCreator.getName(symbol),
                evaluateImpl(content),
                innerIndices));
      }
    }
    return assignments;
  }

  @Override
  public void close() {
    if (!isClosed()) {
      msat_destroy_model(model);
    }
    super.close();
  }

  @Override
  protected Long evalImpl(Long formula) {
    Preconditions.checkState(!isClosed());
    Preconditions.checkState(!prover.isClosed(), "cannot use model after prover is closed");
    return msat_model_eval(model, formula);
  }
}
