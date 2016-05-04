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
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;

import org.sosy_lab.solver.api.BooleanFormula;

import java.util.HashMap;
import java.util.Map;

/**
 * Serialization of the current query held by the solver.
 */
@AutoValue
public abstract class OptimizationQuery {
  public abstract ImmutableSet<BooleanFormula> constraints();

  public abstract ImmutableMap<Integer, OptimizationObjective> objectives();

  public OptimizationQuery addConstraint(BooleanFormula pConstraint) {
    return new AutoValue_OptimizationQuery(
        ImmutableSet.copyOf(Sets.union(constraints(), ImmutableSet.of(pConstraint))), objectives());
  }

  public OptimizationQuery addObjective(OptimizationObjective pObjective, int handle) {
    Map<Integer, OptimizationObjective> m = new HashMap<>(objectives());
    m.put(handle, pObjective);
    return new AutoValue_OptimizationQuery(constraints(), ImmutableMap.copyOf(m));
  }

  public static OptimizationQuery empty() {
    return new AutoValue_OptimizationQuery(
        ImmutableSet.<BooleanFormula>of(), ImmutableMap.<Integer, OptimizationObjective>of());
  }
}
