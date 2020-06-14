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

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import org.sosy_lab.java_smt.basicimpl.AbstractModel.CachingAbstractModel;

class BoolectorModel extends CachingAbstractModel<Long, Long, Long> {

  private final long btor;
  private final BoolectorAbstractProver<?> prover;
  private final BoolectorFormulaCreator bfCreator;
  private boolean closed = false;

  private final ImmutableList<Long> assertedTerms;

  BoolectorModel(
      long btor,
      BoolectorFormulaCreator creator,
      BoolectorAbstractProver<?> pProver,
      Collection<Long> assertedTerms) {
    super(creator);
    this.bfCreator = creator;
    this.btor = btor;
    this.prover = pProver;
    this.assertedTerms = ImmutableList.copyOf(assertedTerms);
  }

  @Override
  public void close() {
    if (!closed) {
      // Technically boolector has no model
      // but you could release all bindings.
      closed = true;
    }
  }

  @Override
  protected ImmutableList<ValueAssignment> toList() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(!prover.isClosed(), "cannot use model after prover is closed");
    // We wait till the Boolector devs give us methods to do this properly.
    // See toList1 for help building this method! (delete toList1 later)
    ImmutableList.Builder<ValueAssignment> assignments = ImmutableList.builder();
    return assignments.build();
  }

  @SuppressWarnings("unused")
  private ImmutableList<ValueAssignment> toList1() {
    Preconditions.checkState(!closed);
    Preconditions.checkState(!prover.isClosed(), "cannot use model after prover is closed");
    ImmutableList.Builder<ValueAssignment> assignments = ImmutableList.builder();
    for (Long formula : assertedTerms) {
      for (Map.Entry<String, Long> entry :
          creator.extractVariablesAndUFs(formula, true).entrySet()) {
        String name = entry.getKey();
        Long var = entry.getValue();
        if (BtorJNI.boolector_is_array(btor, var)) {
          assignments.add(getArrayAssignment(formula));
        } else if (BtorJNI.boolector_is_uf(btor, var)) {
          assignments.add(getUFAssignment(formula));
        } else {
          assignments.add(getConstAssignment(formula));
        }
      }
    }
    return assignments.build();
  }

  private ValueAssignment getConstAssignment(long key) {
    // Boolector does not give back a value "node" (formula), just an assignment string.
    // We have to wait for the new methods and revisit this method!
    List<Object> argumentInterpretation = new ArrayList<>();
    Object value = creator.convertValue(key, evalImpl(key));
    argumentInterpretation.add(value);
    long valueNode;
    if (value.equals(true)) {
      valueNode = BtorJNI.boolector_true(btor);
    } else if (value.equals(false)) {
      valueNode = BtorJNI.boolector_false(btor);
    } else {
      long sort = BtorJNI.boolector_bitvec_sort(btor, BtorJNI.boolector_get_width(btor, key));
      valueNode = BtorJNI.boolector_int(btor, (long) value, sort);
    }
    return new ValueAssignment(
        creator.encapsulateWithTypeOf(key),
        creator.encapsulateWithTypeOf(valueNode),
        creator.encapsulateBoolean(BtorJNI.boolector_eq(btor, key, valueNode)),
        bfCreator.getName(key),
        value,
        argumentInterpretation);
  }

  private ValueAssignment getUFAssignment(long key) {
    List<Object> argumentInterpretation = new ArrayList<>();
    Long value = evalImpl(key); // wrong! use creator.convertValue
    // TODO
    return new ValueAssignment(
        creator.encapsulateWithTypeOf(key),
        creator.encapsulateWithTypeOf(value),
        creator.encapsulateBoolean(BtorJNI.boolector_eq(btor, key, value)),
        bfCreator.getName(key),
        creator.convertValue(key, value),
        argumentInterpretation);
  }

  private ValueAssignment getArrayAssignment(long key) {
    List<Object> argumentInterpretation = new ArrayList<>();
    Long value = evalImpl(key); // wrong! use creator.convertValue
    Long valueNode = null;
    // TODO
    return new ValueAssignment(
        creator.encapsulateWithTypeOf(key),
        creator.encapsulateWithTypeOf(valueNode),
        creator.encapsulateBoolean(BtorJNI.boolector_eq(btor, key, value)),
        bfCreator.getName(key),
        creator.convertValue(key, value),
        argumentInterpretation);
  }

  @Override
  protected Long evalImpl(Long pFormula) {
    Preconditions.checkState(!closed);
    return pFormula;
  }
}
