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
package org.sosy_lab.java_smt.solvers.wrapper.strategy;

import com.google.errorprone.annotations.Immutable;
import java.util.ArrayList;
import java.util.List;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingFormula;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingFormulaStore;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingInfixOperator;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingPrefixOperator;
import org.sosy_lab.java_smt.solvers.wrapper.canonizing.CanonizingVariable;

/**
 * CanonizingStrategies shall be used to canonize {@link CanonizingFormula}s.
 * <p>
 * For better configurability and clearness, it is recommended to implement such strategies as
 * specialized as possible. E.g., do not mix alteration of variable-names, reordering of operands,
 * and constant-propagation into a single strategy.
 */
@Immutable
public interface CanonizingStrategy {

  default CanonizingFormula canonizeInfixOperator(
      FormulaManager pMgr,
      FunctionDeclarationKind pOperator,
      CanonizingFormula pLeft,
      CanonizingFormula pRight,
      FormulaType<?> pReturnType,
      CanonizingFormulaStore pCaller) {
    return new CanonizingInfixOperator(
        pMgr,
        pOperator,
        pLeft.canonize(this, pCaller),
        pRight.canonize(this, pCaller),
        pReturnType);
  }

  default CanonizingFormula canonizePrefixOperator(
      FormulaManager pMgr,
      FunctionDeclarationKind pOperator,
      List<CanonizingFormula> pOperands,
      FormulaType<?> pReturnType,
      CanonizingFormulaStore pCaller) {
    List<CanonizingFormula> args = new ArrayList<>();
    for (CanonizingFormula operandToCanonize : pOperands) {
      args.add(operandToCanonize.canonize(this, pCaller));
    }

    CanonizingPrefixOperator canonizedFormula =
        new CanonizingPrefixOperator(pMgr, pOperator, args, pReturnType);
    return canonizedFormula;
  }

  @SuppressWarnings("unused")
  default CanonizingFormula
      canonizeVariable(
          FormulaManager pMgr,
          String pName,
          FormulaType<?> pType,
          CanonizingFormulaStore pCaller) {
    return new CanonizingVariable(pMgr, pName, pType);
  }
}
