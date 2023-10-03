// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.dreal4;

import com.google.common.base.Preconditions;
import java.util.List;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Config;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Dreal;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Formula;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.FormulaKind;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variables;

public class DReal4QuantifiedFormulaManager
    extends AbstractQuantifiedFormulaManager<
        DRealTerm<?, ?>, Variable.Type.Kind, Config, DRealTerm<?, ?>> {

  protected DReal4QuantifiedFormulaManager(
      FormulaCreator<DRealTerm<?, ?>, Variable.Type.Kind, Config, DRealTerm<?, ?>>
          pFormulaCreator) {
    super(pFormulaCreator);
  }

  @Override
  protected DRealTerm<?, ?> eliminateQuantifiers(DRealTerm<?, ?> pExtractInfo)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("dReal does not support to eliminate quantifiers.");
  }

  // It is allowed to create a quantified Formula with boolean Variables, but as soon as CheckSat
  // is called on a formula with a quantified boolean Variable, dReal returns an error. Therefore,
  // it is not allowed to create a quantifier with a boolean Variable, because if Unsat would be
  // called, an error would be created
  @Override
  public DRealTerm<Formula, FormulaKind.FormulaType> mkQuantifier(
      Quantifier pQ, List<DRealTerm<?, ?>> pVars, DRealTerm<?, ?> pBody) {
    Preconditions.checkArgument(!pVars.isEmpty(), "Empty variable list for quantifier.");
    // create Variables from pVars to create forall formula
    Variables vars = new Variables();
    for (DRealTerm<?, ?> term : pVars) {
      if (term.isVar()) {
        if (term.getType() == Variable.Type.BOOLEAN) {
          throw new UnsupportedOperationException(
              "dReal does not allow to check for Unsat with "
                  + "boolean variable in quantified formula, therefore it is not allowed to create "
                  + "such a formula.");
        }
        vars.insert(term.getVariable());
      } else {
        throw new IllegalArgumentException("It is only possible to bound variables.");
      }
    }
    if (pQ == Quantifier.EXISTS) {
      throw new UnsupportedOperationException("dReal does not support existential quantifiers.");
    } else {
      if (pBody.isFormula()) {
        return new DRealTerm<>(
            Dreal.forall(vars, pBody.getFormula()), pBody.getType(), FormulaKind.FORALL);
      } else if (pBody.isVar()) {
        Variable var = pBody.getVariable();
        if (var.getType() == Variable.Type.BOOLEAN) {
          Formula f = new Formula(var);
          Formula quantified = Dreal.forall(vars, f);
          return new DRealTerm<>(quantified, var.getType(), FormulaKind.FORALL);
        } else {
          throw new IllegalArgumentException(
              "The given Formula is a Variable and the variable is not of type Boolean.");
        }
      } else {
        throw new IllegalArgumentException("The given Formula is not a Formula.");
      }
    }
  }
}
