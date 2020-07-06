// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.z3;

import org.sosy_lab.java_smt.api.SolverException;

/** This exception is thrown by native Z3 code, through our customized JNI bindings. */
class Z3SolverException extends SolverException {

  private static final long serialVersionUID = 9047786707330265032L;

  Z3SolverException(String msg) {
    super(msg);
  }
}
