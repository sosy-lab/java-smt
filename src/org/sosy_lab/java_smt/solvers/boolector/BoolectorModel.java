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

import com.google.common.collect.ImmutableList;
import org.sosy_lab.java_smt.basicimpl.AbstractModel.CachingAbstractModel;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

class BoolectorModel extends CachingAbstractModel<Long, Long, BoolectorEnvironment> {

  private final long model;
  private boolean closed = false;

  BoolectorModel(
      long model,
      FormulaCreator<Long, Long, BoolectorEnvironment, ?> creator) {
    super(creator);
    this.model = model;
  }

  @Override
  public void close() {
    if (!closed) {
      BtorJNI.boolector_delete(model);
      closed = true;
    }
  }

  @Override
  protected ImmutableList<ValueAssignment> toList() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  protected Long evalImpl(Long pFormula) {
    if (BtorJNI.boolector_is_array_var(model, pFormula)) {
      BtorJNI.boolector_array_assignment(model, jarg2, jarg3, jarg4, jarg5);
    } else if (BtorJNI.boolector_is_var(model, pFormula)) {

    } else if (false /* uf var */) {

    } else {
      throw new AssertionError("Unexpected formula: " + pFormula);
    }
  }

}
