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

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.base.Preconditions;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.UserPropagator;
import org.sosy_lab.java_smt.api.PropagatorBackend;

public abstract class AbstractUserPropagator implements UserPropagator  {

  protected @Nullable PropagatorBackend backend;

  @Override
  public void onFinalCheck() {

  }

  @Override
  public void onEquality(BooleanFormula x, BooleanFormula y) {

  }

  @Override
  public void onKnownValue(BooleanFormula expr, BooleanFormula val) {

  }

  @Override
  public final void injectBackend(PropagatorBackend backend) {
    this.backend = Preconditions.checkNotNull(backend);
  }

  @Override
  public void registerExpression(BooleanFormula theoryExpr) {
    Preconditions.checkState(backend != null);
    backend.registerExpression(theoryExpr);
  }

}
