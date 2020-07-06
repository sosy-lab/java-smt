// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl.reusableStack;

import org.sosy_lab.java_smt.api.ProverEnvironment;

public class ReusableStackTheoremProver extends ReusableStackAbstractProver<Void, ProverEnvironment>
    implements ProverEnvironment {

  public ReusableStackTheoremProver(ProverEnvironment pDelegate) {
    super(pDelegate);
  }
}
