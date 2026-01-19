// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

/**
 * Represents the various rounding modes that can be applied when converting or manipulating
 * floating-point values and formulas. These modes define how results are rounded when an exact
 * representation is not possible due to precision limits of the target format.
 */
public enum FloatingPointRoundingMode {
  NEAREST_TIES_TO_EVEN,
  NEAREST_TIES_AWAY,
  TOWARD_POSITIVE,
  TOWARD_NEGATIVE,
  TOWARD_ZERO
}
