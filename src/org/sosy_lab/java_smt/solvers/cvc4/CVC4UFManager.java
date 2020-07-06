// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc4;

import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.Type;
import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;

class CVC4UFManager extends AbstractUFManager<Expr, Expr, Type, ExprManager> {

  CVC4UFManager(CVC4FormulaCreator pCreator) {
    super(pCreator);
  }
}
