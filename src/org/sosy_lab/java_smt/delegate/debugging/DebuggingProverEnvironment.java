// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.delegate.debugging.DebuggingSolverContext.NodeManager;

public class DebuggingProverEnvironment extends DebuggingBasicProverEnvironment<Void>
    implements ProverEnvironment {
  public DebuggingProverEnvironment(
      BasicProverEnvironment<Void> pDelegate, NodeManager pLocalFormulas) {
    super(pDelegate, pLocalFormulas);
  }
}
