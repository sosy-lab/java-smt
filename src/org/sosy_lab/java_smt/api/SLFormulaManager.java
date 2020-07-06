// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

/**
 * The {@link SLFormulaManager} can build formulae for separation logic.
 *
 * <p>Info: A {@link ProverEnvironment} only supports the assertion of well-typed SL-formulae, i.e.
 * all formulae for one heap need to use matching types (sorts) for the AdressFormulae and
 * ValueFormulae. The user has to take care of this, otherwise the {@link ProverEnvironment}
 * complains at runtime!
 */
@SuppressWarnings("MethodTypeParameterName")
public interface SLFormulaManager {

  BooleanFormula makeStar(BooleanFormula f1, BooleanFormula f2);

  <AF extends Formula, VF extends Formula> BooleanFormula makePointsTo(AF ptr, VF to);

  BooleanFormula makeMagicWand(BooleanFormula f1, BooleanFormula f2);

  <AF extends Formula, VF extends Formula, AT extends FormulaType<AF>, VT extends FormulaType<VF>>
      BooleanFormula makeEmptyHeap(AT pAdressType, VT pValueType);

  <AF extends Formula, AT extends FormulaType<AF>> AF makeNilElement(AT pAdressType);
}
