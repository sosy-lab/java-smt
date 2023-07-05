// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import opensmt.Logic;
import opensmt.PTRef;
import opensmt.SRef;
import opensmt.SymRef;
import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;

class OpenSmtUFManager extends AbstractUFManager<PTRef, SymRef, SRef, Logic> {

  OpenSmtUFManager(OpenSmtFormulaCreator pCreator) {
    super(pCreator);
  }
}
