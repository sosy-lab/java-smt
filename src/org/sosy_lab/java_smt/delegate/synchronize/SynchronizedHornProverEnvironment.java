// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.synchronize;

import java.util.Collection;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.HornProverEnvironment;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;

class SynchronizedHornProverEnvironment extends SynchronizedBasicProverEnvironment<Void>
    implements HornProverEnvironment {

  private final HornProverEnvironment delegate;

  SynchronizedHornProverEnvironment(
      HornProverEnvironment pDelegate, SolverContext pSync) {
    super(pDelegate, pSync);
    delegate = pDelegate;
  }
}
