// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

/**
 * Wrapper-classes to guarantee identical behavior for all solvers. If a solver does not support
 * {@link org.sosy_lab.java_smt.api.BasicProverEnvironment#isUnsatWithAssumptions}, we wrap it in a
 * (subclass of) BasicProverWithAssumptionsWrapper, whose task it is to keep the assumptions as long
 * on the solver's stack as no other operation accesses it. It allows to compute interpolants and
 * unsat cores. without direct support from the solver.
 */
package org.sosy_lab.java_smt.basicimpl.withAssumptionsWrapper;
