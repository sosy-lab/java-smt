// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import static org.sosy_lab.java_smt.api.FormulaType.getSinglePrecisionFloatingPointType;

import com.google.common.testing.AbstractPackageSanityTests;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;

public class PackageSanityTest extends AbstractPackageSanityTests {

  {
    setDistinctValues(FormulaType.class, FormulaType.BooleanType, FormulaType.IntegerType);
    setDistinctValues(
        FloatingPointType.class,
        FloatingPointType.getSinglePrecisionFloatingPointType(),
        FloatingPointType.getDoublePrecisionFloatingPointType());
    setDefault(FloatingPointType.class, getSinglePrecisionFloatingPointType());
  }
}
