// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import com.google.errorprone.annotations.Immutable;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;

/** An arbitrary SMT formula. */
@Immutable
public interface Formula {

  /**
   * returns an arbitrary representation of the formula, might be human- or machine-readable.
   *
   * <p>We do not guarantee that the returned String is in any way related to the formula. The
   * solver might apply escaping or even un-escaping. A user should not use the returned String for
   * further processing. For analyzing formulas, we recommend to use a {@link FormulaVisitor}.
   */
  @Override
  String toString();

  /**
   * checks whether the other object is a formula of the same structure. Does not apply an expensive
   * SAT-check to check equisatisfiability.
   *
   * <p>Two formulas that are structured in the same way, are determined as "equal". Due to
   * transformations and simplifications, two equisatisfiable formulas with different structure
   * might not be determined as "equal".
   */
  @Override
  boolean equals(Object other);

  /** returns a valid hashCode satisfying the constraints given by {@link #equals}. */
  @Override
  int hashCode();
}
