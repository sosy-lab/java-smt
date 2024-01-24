// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.bitwuzla;

import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;

public class BitwuzlaUFManager extends AbstractUFManager<Long, BitwuzlaDeclaration, Long, Long> {
  protected BitwuzlaUFManager(FormulaCreator<Long, Long, Long, BitwuzlaDeclaration> pCreator) {
    super(pCreator);
  }
}
