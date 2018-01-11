/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
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
 * respond in a timely manner (or at all) to shutdown or interrupt requests.
 */
public interface ProverEnvironment extends BasicProverEnvironment<Void> {}
