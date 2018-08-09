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

/**
 * Wrapper-classes to guarantee identical behavior for all solvers. If a solver does not support
 * {@link org.sosy_lab.java_smt.api.BasicProverEnvironment#isUnsatWithAssumptions}, we wrap it in a
 * (subclass of) BasicProverWithAssumptionsWrapper, whose task it is to keep the assumptions as long
 * on the solver's stack as no other operation accesses it. It allows to compute interpolants and
 * unsat cores. without direct support from the solver.
 */
package org.sosy_lab.java_smt.basicimpl.withAssumptionsWrapper;
