// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

/**
 * JavaSMT: a generic SMT solver API.
 *
 * <p>{@link org.sosy_lab.java_smt.SolverContextFactory} is a package entry point, which creates a
 * {@link org.sosy_lab.java_smt.api.SolverContext} object. All operations on formulas are performed
 * using managers, available through the context object.
 *
 * <p>All interfaces which form the public API are located in the <a
 * href="api/package-summary.html">API package</a>.
 */
@com.google.errorprone.annotations.CheckReturnValue
@javax.annotation.ParametersAreNonnullByDefault
@org.sosy_lab.common.annotations.FieldsAreNonnullByDefault
@org.sosy_lab.common.annotations.ReturnValuesAreNonnullByDefault
package org.sosy_lab.java_smt;
