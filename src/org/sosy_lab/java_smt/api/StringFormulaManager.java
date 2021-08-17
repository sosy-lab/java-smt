// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2021 Alejandro Serrano Mena
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import com.google.errorprone.annotations.CanIgnoreReturnValue;
import java.util.Collection;
import java.util.Set;
import java.util.stream.Collector;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaTransformationVisitor;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

/** Manager for dealing with string formulas. */
public interface StringFormulaManager {

  /**
   * Returns a {@link StringFormula} representing the given constant.
   *
   * @param value the boolean value the returned <code>Formula</code> should represent
   * @return a Formula representing the given value
   */
  StringFormula makeString(String value);

  /**
   * Creates a variable with exactly the given name.
   *
   * <p>Please make sure that the given name is valid in SMT-LIB2. Take a look at {@link
   * FormulaManager#isValidName} for further information.
   *
   * <p>This method does not quote or unquote the given name, but uses the plain name "AS IS".
   * {@link Formula#toString} can return a different String than the given one.
   */
  StringFormula makeVariable(String pVar);

  StringFormula equal(StringFormula str1, StringFormula str2);
}
