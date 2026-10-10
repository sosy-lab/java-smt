// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableList;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext;

class SynchronizedModel extends SynchronizedEvaluator implements Model {

  private final Model delegate;
  private final SolverContext sync;

  SynchronizedModel(Model pDelegate, SolverContext pSync) {
    super(pDelegate, pSync);
    delegate = checkNotNull(pDelegate);
    sync = checkNotNull(pSync);
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    synchronized (sync) {
      return delegate.asList();
    }
  }
}
