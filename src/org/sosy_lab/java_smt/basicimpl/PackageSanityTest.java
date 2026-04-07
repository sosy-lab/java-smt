// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.testing.AbstractPackageSanityTests;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.FormulaType;

@SuppressWarnings("resource")
public class PackageSanityTest extends AbstractPackageSanityTests {

  {
    setDistinctValues(FormulaType.class, FormulaType.BooleanType, FormulaType.IntegerType);
    setDefault(ShutdownNotifier.class, ShutdownManager.create().getNotifier());
    try {
      // Due to solver independent interpolation we need a default solver for AbstractSolverContext
      // Use Princess as it is always available
      // TODO: look into this some more. Can we get rid of this? What is going on with the
      //  ressource suppression?
      setDefault(
          AbstractSolverContext.class,
          (AbstractSolverContext) SolverContextFactory.createSolverContext(Solvers.PRINCESS));
    } catch (InvalidConfigurationException e) {
      throw new RuntimeException(e);
    }
    ignoreClasses(c -> c.equals(InterpolatingProverDelegate.class));
  }
}
