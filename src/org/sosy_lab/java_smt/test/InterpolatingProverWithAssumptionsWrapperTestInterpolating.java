// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.basicimpl.withAssumptionsWrapper.InterpolatingProverWithAssumptionsWrapper;
import org.sosy_lab.java_smt.solvers.opensmt.Logics;

public class InterpolatingProverWithAssumptionsWrapperTestInterpolating
    extends InterpolatingSolverFormulaWithAssumptionsTest {

  // INFO: OpenSmt only support interpolation for QF_LIA, QF_LRA and QF_UF
  @Override
  protected Logics logicToUse() {
    return Logics.QF_LIA;
  }

  @Override
  @SuppressWarnings({"unchecked", "rawtypes", "resource"})
  protected <T> InterpolatingProverEnvironment<T> newEnvironmentForTest() {
    final InterpolatingProverEnvironment<?> proverEnvironment =
        context.newProverEnvironmentWithInterpolation();
    return new InterpolatingProverWithAssumptionsWrapper(proverEnvironment, mgr);
  }
}
