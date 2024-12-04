/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.test;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.UltimateEliminator;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import org.junit.Test;

public class UltimateEliminatorTest {

  // private IUltimateServiceProvider provider;

  @Test
  public void test1() {
    // Script is SMTInterpol Script, e.g. new SMTInterpol(null, options)
    Script script = null;
    new UltimateEliminator(null, null, script);
  }
}
