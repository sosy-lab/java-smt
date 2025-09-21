// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.util.Map;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.solvers.opensmt.api.Logic;
import org.sosy_lab.java_smt.solvers.opensmt.api.Model;
import org.sosy_lab.java_smt.solvers.opensmt.api.PTRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SRef;

public class OpenSmtModel extends AbstractModel<PTRef, SRef, Logic> {

  private final Logic osmtLogic;
  private final Model osmtModel;

  private final ImmutableList<ValueAssignment> model;

  OpenSmtModel(
      FormulaManager pMgr, OpenSmtAbstractProver<?> pProver, OpenSmtFormulaCreator pCreator) {
    super(pMgr, pProver, pCreator);

    osmtLogic = pCreator.getEnv();
    osmtModel = pProver.getOsmtSolver().getModel();

    // We need to generate and save this at construction time as OpenSMT has no functionality to
    // give a persistent reference to the model. If the SMT engine is used somewhere else, the
    // values we get out of it might change!
    model = super.asList();
  }

  @Override
  public PTRef evalImpl(PTRef f) {
    Preconditions.checkState(!isClosed());
    Map<String, PTRef> userDeclarations = creator.extractVariablesAndUFs(f, true);

    // FIXME: rewrite to use checkCompatibility from AbstractProver

    for (PTRef term : userDeclarations.values()) {
      SRef sort = osmtLogic.getSortRef(term);
      if (osmtLogic.isArraySort(sort)) {
        // INFO: Disable model generation if arrays are used
        // https://github.com/usi-verification-and-security/opensmt/issues/630
        throw new UnsupportedOperationException(
            "OpenSMT does not support model generation when arrays are used");
      }
    }
    return osmtModel.evaluate(f);
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return model;
  }
}
