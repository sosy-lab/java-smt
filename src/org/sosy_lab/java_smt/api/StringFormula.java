// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Alejandro Serrano Mena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import com.google.errorprone.annotations.Immutable;

/** A formula of the string sort. */
@Immutable
public interface StringFormula extends Formula {}
