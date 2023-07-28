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

package org.sosy_lab.java_smt.solvers.dreal4;

import com.google.common.collect.ImmutableList;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Box;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Context;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable.Type;


public class DReal4Model extends AbstractModel<DRealTerm<?, ?>, Type, Context> {

  private final Box model;
  private final DReal4FormulaCreator formulaCreator;
  private final DReal4TheoremProver prover;

  DReal4Model(DReal4TheoremProver prover, DReal4FormulaCreator pCreator, Box model) {
    super(prover, pCreator);
    this.model = model;
    this.prover = prover;
    this.formulaCreator = pCreator;
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return null;
  }

  @Override
  protected @Nullable DRealTerm<?, ?> evalImpl(DRealTerm<?, ?> formula) {
    return null;
  }

}