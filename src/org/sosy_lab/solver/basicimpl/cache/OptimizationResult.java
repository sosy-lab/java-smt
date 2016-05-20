/*
 *
 *  *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  *  This file is part of JavaSMT.
 *  *
 *  *  Copyright (C) 2007-2016  Dirk Beyer
 *  *  All rights reserved.
 *  *
 *  *  Licensed under the Apache License, Version 2.0 (the "License");
 *  *  you may not use this file except in compliance with the License.
 *  *  You may obtain a copy of the License at
 *  *
 *  *      http://www.apache.org/licenses/LICENSE-2.0
 *  *
 *  *  Unless required by applicable law or agreed to in writing, software
 *  *  distributed under the License is distributed on an "AS IS" BASIS,
 *  *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  *  See the License for the specific language governing permissions and
 *  *  limitations under the License.
 *
 *
 */

package org.sosy_lab.solver.basicimpl.cache;

import com.google.auto.value.AutoValue;
import com.google.common.base.Optional;
import com.google.common.collect.ImmutableMap;

import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.solver.api.OptimizationProverEnvironment.OptStatus;

import java.util.HashMap;
import java.util.Map;

/**
 * Result of the optimization query.
 */
@AutoValue
public abstract class OptimizationResult {

  /**
   * The result of the optimization problem, does not depend on the objectives.
   */
  public abstract OptStatus result();

  /**
   * Cached values of the objective functions.
   */
  public abstract ImmutableMap<Integer, Optional<Rational>> objectiveValues();

  /**
   * Cached stored model.
   */
  public abstract Optional<CachedModel> model();

  public OptimizationResult withObjectiveValue(int handle, Optional<Rational> value) {
    Map<Integer, Optional<Rational>> map = new HashMap<>(objectiveValues());
    map.put(handle, value);

    return new AutoValue_OptimizationResult(result(), ImmutableMap.copyOf(map), model());
  }

  public OptimizationResult withModel(CachedModel pModel) {
    return new AutoValue_OptimizationResult(result(), objectiveValues(), Optional.of(pModel));
  }

  static OptimizationResult of(OptStatus result) {
    return new AutoValue_OptimizationResult(result, ImmutableMap.of(), Optional.absent());
  }
}
