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
 * A formula of the array sort.
 *
 * @param <TI> Index type.
 * @param <TE> Element type.
 */
@SuppressWarnings("InterfaceTypeParameterName")
@Immutable
public interface ArrayFormula<TI extends Formula, TE extends Formula> extends Formula {}
