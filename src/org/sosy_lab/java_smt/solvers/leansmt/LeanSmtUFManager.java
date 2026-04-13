// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.leansmt;

import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;

final class LeanSmtUFManager
    extends AbstractUFManager<Long, LeanSmtFunctionDecl, LeanSmtType, Long> {

  LeanSmtUFManager(LeanSmtFormulaCreator pCreator) {
    super(pCreator);
  }
}
