// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl.withAssumptionsWrapper;

import org.sosy_lab.java_smt.api.ProverEnvironment;

public class ProverWithAssumptionsWrapper
    extends BasicProverWithAssumptionsWrapper<Void, ProverEnvironment>
    implements ProverEnvironment {

  public ProverWithAssumptionsWrapper(ProverEnvironment pDelegate) {
    super(pDelegate);
  }
}
