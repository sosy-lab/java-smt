// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api.visitors;

import org.sosy_lab.java_smt.api.Formula;

/**
 * Like {@link DefaultFormulaVisitor}, but throws {@link UnsupportedOperationException} on
 * unexpected formula types.
 */
public abstract class ExpectedFormulaVisitor<R> extends DefaultFormulaVisitor<R> {

  @Override
  protected final R visitDefault(Formula f) {
    throw new UnsupportedOperationException();
  }
}
