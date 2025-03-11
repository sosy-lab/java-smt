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
import org.sosy_lab.java_smt.api.FormulaType;

public class PackageSanityTest extends AbstractPackageSanityTests {

  {
    setDistinctValues(FormulaType.class, FormulaType.BooleanType, FormulaType.IntegerType);
    setDefault(ShutdownNotifier.class, ShutdownManager.create().getNotifier());
    setDefault(FormulaType.BitvectorType.class, FormulaType.getBitvectorTypeWithSize(32));
    setDefault(
        FormulaType.FloatingPointType.class, FormulaType.getSinglePrecisionFloatingPointType());
    ignoreClasses(c -> c.getSimpleName().equals("ModelException"));
    ignoreClasses(c -> c.getSimpleName().equals("BinaryModel"));
    ignoreClasses(c -> c.getSimpleName().equals("GeneratorException"));
  }
}
