/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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

package org.sosy_lab.java_smt.solvers.dreal4;

import java.util.List;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.basicimpl.AbstractQuantifiedFormulaManager;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Context;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variable.Type;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.Variables;
import org.sosy_lab.java_smt.solvers.dreal4.drealjni.dreal;

public class DReal4QuantifiedFormulaManager extends AbstractQuantifiedFormulaManager<DRealTerm,
    Type, Context, DRealTerm> {

  protected DReal4QuantifiedFormulaManager(FormulaCreator<DRealTerm, Type, Context, DRealTerm> pFormulaCreator) {
    super(pFormulaCreator);
  }

  @Override
  protected DRealTerm eliminateQuantifiers(DRealTerm pExtractInfo)
      throws SolverException, InterruptedException {
    throw new UnsupportedOperationException("dReal can not eliminate quantifiers.");
  }

  @Override
  public DRealTerm mkQuantifier(Quantifier pQ, List<DRealTerm> pVars, DRealTerm pBody) {
    if (pVars.isEmpty()) {
      throw new IllegalArgumentException("Empty variable llist for quantifier.");
    } else if (pQ == Quantifier.EXISTS) {
      // Doch eigentlich schon, aber noch nicht gefunden??
      throw new UnsupportedOperationException("dReal does not support exist??");
    } else {
      Variables vars = new Variables();
      for (DRealTerm term : pVars) {
        if (term.isVar()) {
          vars.insert(term.getVariable());
        } else {
          throw new IllegalArgumentException("This term is not a Variable and will be "
              + "skipped.");
        }
      }
      if (pBody.isFormula()) {
        return new DRealTerm(null, null, dreal.forall(vars, pBody.getFormula()), pBody.getType());
      } else {
        throw new IllegalArgumentException("The given Formula is not a Formula.");
      }
    }
  }

}
