// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import org.sosy_lab.common.ShutdownNotifier;

/**
 * An interface to an incremental SMT solver with methods for pushing and popping formulas as well
 * as SAT checks. Instances of this class can be used once for a series of related queries. After
 * that, the {@link #close} method should be called (preferably using the try-with-resources
 * syntax). All methods are expected to throw {@link IllegalStateException}s after close was called.
 *
 * <p>All solving methods are expected to throw {@link SolverException} if the solver fails to solve
 * the given query, and {@link InterruptedException} if a thread interrupt was requested or a
 * shutdown request via the {@link ShutdownNotifier}. It is not guaranteed, though, that solvers
 * respond in a timely manner (or at all) to shut down or interrupt requests.
 */
public interface ProverEnvironment extends BasicProverEnvironment<Void> {}
