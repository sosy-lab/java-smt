/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
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
