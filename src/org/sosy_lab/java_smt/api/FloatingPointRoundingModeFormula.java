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
 * Formula representing a rounding mode for floating-point operations. This is currently unused by
 * the API but necessary for traversal of formulas with such terms.
 */
@Immutable
public interface FloatingPointRoundingModeFormula extends Formula {}
