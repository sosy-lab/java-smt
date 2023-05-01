// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import com.google.common.base.Preconditions;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableSet;
import java.util.Set;
import org.sosy_lab.java_smt.api.FormulaType.EnumerationFormulaType;

/**
 * This interface represents the theory of enumeration, i.e., datatype of limited domain sort (as
 * defined in the SMTLIB2 standard).
 */
public interface EnumerationFormulaManager {

  /**
   * Declare an enumeration.
   *
   * @param pName the name of the enumeration type.
   * @param ppElementNames names for all individual elements of this enumeration type.
   */
  EnumerationFormulaType declareEnumeration(String pName, Set<String> ppElementNames);

  /**
   * @see #declareEnumeration(String, Set)
   */
  default EnumerationFormulaType declareEnumeration(String pName, String... pElementNames) {
    final Set<String> elements = ImmutableSet.copyOf(pElementNames);
    Preconditions.checkArgument(
        pElementNames.length == elements.size(),
        "An enumeration type requires pairwise distinct elements. "
            + "The following elements were given multiple times: %s",
        FluentIterable.from(pElementNames).filter(e -> !elements.contains(e)));
    return declareEnumeration(pName, elements);
  }

  /**
   * Creates a constant of given enumeration type with exactly the given name. This constant
   * (symbol) needs to be an element from the given enumeration type.
   */
  EnumerationFormula makeConstant(String pName, EnumerationFormulaType pType);

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
