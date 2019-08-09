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
import org.sosy_lab.java_smt.basicimpl.AbstractModel.CachingAbstractModel;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

class BoolectorModel extends CachingAbstractModel<Long, Long, BoolectorEnvironment> {

  private final static char BOOLECTOR_VARIABLE_ARBITRARI_REPLACEMENT = '1';

  private final long btor;
  private boolean closed = false;

  BoolectorModel(
      long btor,
      FormulaCreator<Long, Long, BoolectorEnvironment, ?> creator) {
    super(creator);
    this.btor = btor;
  }

  @Override
  public void close() {
    if (!closed) {
      System.out.println("Model");
      BtorJNI.boolector_delete(btor);
      closed = true;
    }
  }

  @Override
  protected ImmutableList<ValueAssignment> toList() {
    Preconditions.checkState(!closed);

    return null;
  }

  @Override
  protected Long evalImpl(Long pFormula) {
    Preconditions.checkState(!closed);
    // Preconditions.checkState(!prover.closed, "cannot use model after prover is closed");
    if (BtorJNI.boolector_is_var(btor, pFormula)) {
      String assignment = BtorJNI.boolector_bv_assignment(btor, pFormula);
      return parseLong(assignment);
    } else if (false /* do i need uf/array here? */) {
      return (long) 0;
    } else {
      throw new AssertionError("Unexpected formula: " + pFormula);
    }
  }

  /**
   * Boolector puts out Strings containing 1,0 or x that have to be parsed. If you want different
   * values for x, change it in the constant! (BOOLECTOR_VARIABLE_ARBITRARI_REPLACEMENT)
   *
   * @param assignment String with the assignment of Boolector var.
   * @return long representation of assignment String.
   */
  private Long parseLong(String assignment) {
    try {
      return Long.parseLong(assignment);
    } catch (NumberFormatException e) {
      char[] charArray = assignment.toCharArray();
      for (int i = 0; i < charArray.length; i++) {
        if (charArray[i] == 'x') {
          charArray[i] = BOOLECTOR_VARIABLE_ARBITRARI_REPLACEMENT;
        } else if (charArray[i] != '0' && charArray[i] != '1') {
          throw new IllegalArgumentException(
              "Boolector gave back an assignment that is not parseable.");
        }
      }
      return Long.parseLong(charArray.toString());
    }
  }

}
