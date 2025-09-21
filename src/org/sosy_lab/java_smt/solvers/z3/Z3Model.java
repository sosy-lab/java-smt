// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.microsoft.z3.Native;
import com.microsoft.z3.Native.LongPtr;
import com.microsoft.z3.Z3Exception;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.basicimpl.AbstractProver;

final class Z3Model extends AbstractModel<Long, Long, Long> {

  private final long z3model;
  private final long z3context;
  private final Z3FormulaCreator z3creator;

  private final ImmutableList<ValueAssignment> assignments;

  Z3Model(
      AbstractProver<?> pProver,
      long z3context,
      long z3model,
      Z3FormulaManager pMgr,
      Z3FormulaCreator pCreator) {
    super(pMgr, pProver, pCreator);
    Native.modelIncRef(z3context, z3model);
    this.z3model = z3model;
    this.z3context = z3context;
    this.z3creator = pCreator;

    assignments = super.asList();
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return assignments;
  }

  @Override
  public void close() {
    if (!isClosed()) {
      Native.modelDecRef(z3context, z3model);
    }
    super.close();
  }

  @Override
  @Nullable
  protected Long evalImpl(Long formula) {
    LongPtr resultPtr = new LongPtr();
    boolean satisfiableModel;
    try {
      satisfiableModel = Native.modelEval(z3context, z3model, formula, false, resultPtr);
    } catch (Z3Exception e) {
      throw z3creator.handleZ3ExceptionAsRuntimeException(e);
    }
    Preconditions.checkState(satisfiableModel);
    if (resultPtr.value == 0) {
      // unknown evaluation
      return null;
    } else {
      Native.incRef(z3context, resultPtr.value);
      return resultPtr.value;
    }
  }
}
