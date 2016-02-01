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

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.base.Function;
import com.google.common.base.Verify;
import com.google.common.collect.UnmodifiableIterator;

import org.sosy_lab.solver.api.Model.ValueAssignment;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

/**
 * Helper class for writing model iterators.
 */
public class TermExtractionModelIterator<E> extends UnmodifiableIterator<ValueAssignment> {
  private final Iterator<Entry<E, Object>> valuesIterator;
  private final FormulaCreator<E, ?, ?> creator;
  private final Function<E, Object> evaluator;

  public TermExtractionModelIterator(
      FormulaCreator<E, ?, ?> creator,
      Function<E, Object> evaluator,
      Collection<E> assertedTerms) {
    checkNotNull(assertedTerms);
    this.creator = checkNotNull(creator);
    this.evaluator = checkNotNull(evaluator);

    Map<E, Object> values = new HashMap<>();
    for (E t : assertedTerms) {
      for (E key : creator.extractVariablesAndUFs(t, true).values()) {
        Object value = evaluator.apply(key);
        if (value == null) {
          continue;
        }
        Object existingValue = values.get(key);
        Verify.verify(
            existingValue == null || value.equals(existingValue),
            "Duplicate values for model entry %s: %s and %s",
            key,
            existingValue,
            value);
        values.put(key, value);
      }
    }
    valuesIterator = values.entrySet().iterator();
  }

  @Override
  public boolean hasNext() {
    return valuesIterator.hasNext();
  }

  @Override
  public ValueAssignment next() {
    Entry<E, Object> entry = valuesIterator.next();
    return new ValueAssignment(creator.encapsulateWithTypeOf(entry.getKey()), entry.getValue());
  }
}
