// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.delegate.debugging;

import java.util.Set;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.ProverEnvironment;

public class DebuggingProverEnvironment extends DebuggingBasicProverEnvironment<Void>
    implements ProverEnvironment {
  public DebuggingProverEnvironment(
      BasicProverEnvironment<Void> pDelegate, Set<Formula> pLocalFormulas) {
    super(pDelegate, pLocalFormulas);
  }
}
