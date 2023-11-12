// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;
import org.sosy_lab.java_smt.solvers.opensmt.api.Logic;
import org.sosy_lab.java_smt.solvers.opensmt.api.PTRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SymRef;

class OpenSmtUFManager extends AbstractUFManager<PTRef, SymRef, SRef, Logic> {

  OpenSmtUFManager(OpenSmtFormulaCreator pCreator) {
    super(pCreator);
  }
}
