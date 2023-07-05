// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import java.util.EnumSet;
import java.util.Set;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.LogicFeatures;
import org.sosy_lab.java_smt.basicimpl.withAssumptionsWrapper.InterpolatingProverWithAssumptionsWrapper;

public class InterpolatingProverWithAssumptionsWrapperTest
    extends SolverFormulaWithAssumptionsTest {

  // INFO: OpenSmt only support interpolation for QF_LIA, QF_LRA and QF_UF
  @Override
  protected Set<LogicFeatures> logicToUse() {
    return EnumSet.of(LogicFeatures.HAS_INTEGERS);
  }

  @Override
  @SuppressWarnings({"unchecked", "rawtypes", "resource"})
  protected <T> InterpolatingProverEnvironment<T> newEnvironmentForTest() {
    final InterpolatingProverEnvironment<?> proverEnvironment =
        context.newProverEnvironmentWithInterpolation();
    return new InterpolatingProverWithAssumptionsWrapper(proverEnvironment, mgr);
  }
}
