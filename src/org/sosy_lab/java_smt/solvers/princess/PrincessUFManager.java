// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import ap.parser.IExpression;
import ap.types.Sort;
import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;

class PrincessUFManager
    extends AbstractUFManager<IExpression, PrincessFunctionDeclaration, Sort, PrincessEnvironment> {

  PrincessUFManager(PrincessFormulaCreator creator) {
    super(creator);
  }
}
