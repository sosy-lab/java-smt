// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.HornProverEnvironment;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverException;

class DebuggingHornProverEnvironment extends DebuggingBasicProverEnvironment<Void>
    implements HornProverEnvironment {
  private final HornProverEnvironment delegate;
  private final DebuggingAssertions debugging;

  DebuggingHornProverEnvironment(
      HornProverEnvironment pDelegate, DebuggingAssertions pDebugging) {
    super(pDelegate, pDebugging);
    delegate = checkNotNull(pDelegate);
    debugging = pDebugging;
  }
}
