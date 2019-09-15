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
package org.sosy_lab.java_smt.solvers.yices2;

import static org.sosy_lab.java_smt.solvers.yices2.Yices2NativeApi.yices_free_model;

import com.google.common.collect.ImmutableList;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.basicimpl.AbstractModel.CachingAbstractModel;

public class Yices2Model extends CachingAbstractModel<Integer, Integer, Long> {

  private final long model;
  private final Yices2TheoremProver prover;
  private final Yices2FormulaCreator creator;

  protected Yices2Model(long model, Yices2TheoremProver prover, Yices2FormulaCreator pCreator) {
    super(pCreator);
    // TODO Auto-generated constructor stub
    this.model = model;
    this.prover = prover;
    this.creator = pCreator;
  }

  @Override
  public void close() {
    // TODO Auto-generated method stub
    yices_free_model(model);
  }

  @Override
  protected ImmutableList<ValueAssignment> toList() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected @Nullable Integer evalImpl(Integer pFormula) {
    // TODO Auto-generated method stub
    return null;
  }
}

