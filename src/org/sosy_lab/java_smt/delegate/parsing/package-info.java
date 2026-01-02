// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

/* Adds checks that help find common user errors.
 * The classes from this package ensure that objects are only used on the thread that created
 * them, and that formulas are not used out of the context that created them.
 */
@com.google.errorprone.annotations.CheckReturnValue
@javax.annotation.ParametersAreNonnullByDefault
@org.sosy_lab.common.annotations.FieldsAreNonnullByDefault
@org.sosy_lab.common.annotations.ReturnValuesAreNonnullByDefault
package org.sosy_lab.java_smt.delegate.parsing;
