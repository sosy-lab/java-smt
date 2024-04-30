// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.dreal4;

import org.sosy_lab.java_smt.basicimpl.AbstractUFManager;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Config;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;

public class DReal4UFManager
    extends AbstractUFManager<DRealTerm<?, ?>, DRealTerm<?, ?>, Variable.Type.Kind, Config> {

  DReal4UFManager(DReal4FormulaCreator pCreator) {
    super(pCreator);
  }
}
