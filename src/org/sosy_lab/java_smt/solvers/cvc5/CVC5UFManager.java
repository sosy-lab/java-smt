// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.cvc5;

import io.github.cvc5.Solver;
import io.github.cvc5.Sort;
import io.github.cvc5.Term;
import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;

class CVC5UFManager extends AbstractUFManager<Term, Term, Sort, Solver> {

  CVC5UFManager(CVC5FormulaCreator pCreator) {
    super(pCreator);
  }
}
