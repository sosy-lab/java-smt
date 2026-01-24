// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import com.google.errorprone.annotations.Immutable;

/**
 * Formula representing a rounding mode for floating-point operations.
 *
 * <p>Rounding mode formulas are used by floating-point formulas to select the rounding mode for the
 * operation. Use {@link FloatingPointFormulaManager#makeRoundingMode(FloatingPointRoundingMode)} to
 * wrap a {@link org.sosy_lab.java_smt.api.FloatingPointRoundingMode} value inside a new formula.
 *
 * <p>This class is rarely used in the API but necessary to support visitor traversal of formulas
 * with certain floating-point operations, where JavaSMT provides the rounding mode as Formula-based
 * argument.
 */
@Immutable
public interface FloatingPointRoundingModeFormula extends Formula {}
