// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import java.util.List;
import org.sosy_lab.java_smt.api.FormulaType.EnumerationFormulaType;

/**
 * This interface represents the theory of enumeration, i.e., datatype of limited domain sort (as
 * defined in the SMTLIB2 standard)
 */
public interface EnumerationFormulaManager {

  /**
   * Declare an enumeration.
   *
   * @param name the name of the enumeration type.
   * @param elementNames names for all individual elements of this enumeration type.
   */
  EnumerationFormulaType declareEnumeration(String name, List<String> elementNames);

  /**
   * @see #declareEnumeration(String, List)
   */
  EnumerationFormulaType declareEnumeration(String name, String... elementNames);

  /**
   * Creates a constant of given enumeration type with exactly the given name. This constant
   * (symbol) needs to be an element from the given enumeration type.
   */
  EnumerationFormula makeConstant(String pVar, EnumerationFormulaType pType);

  /**
   * Creates a variable of given enumeration type with exactly the given name.
   *
   * <p>This variable (symbol) represents a "String" for which the SMT solver needs to find a model.
   *
   * <p>Please make sure that the given name is valid in SMT-LIB2. Take a look at {@link
   * FormulaManager#isValidName} for further information.
   *
   * <p>This method does not quote or unquote the given name, but uses the plain name "AS IS".
   * {@link Formula#toString} can return a different String than the given one.
   */
  EnumerationFormula makeVariable(String pVar, EnumerationFormulaType pType);

  /**
   * Make a {@link BooleanFormula} that represents the equality of two {@link EnumerationFormula} of
   * identical enumeration type.
   */
  BooleanFormula equivalence(EnumerationFormula pEnumeration1, EnumerationFormula pEnumeration2);
}
