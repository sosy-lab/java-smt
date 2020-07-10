// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

/**
 * The classes of this package wrap the whole solver context and all corresponding proving
 * environment and synchronize all accesses to it.
 *
 * <p>This allows us to use a plain sequential solver in a concurrent context, i.e., we can create
 * formulae and solve queries from multiple interleaving threads without any synchronization from
 * the user.
 */
@com.google.errorprone.annotations.CheckReturnValue
@javax.annotation.ParametersAreNonnullByDefault
@org.sosy_lab.common.annotations.FieldsAreNonnullByDefault
@org.sosy_lab.common.annotations.ReturnValuesAreNonnullByDefault
package org.sosy_lab.java_smt.delegate.synchronize;
