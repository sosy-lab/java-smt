// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import com.google.common.base.Preconditions;
import org.sosy_lab.java_smt.basicimpl.AbstractEvaluator;
import org.sosy_lab.java_smt.solvers.opensmt.api.Logic;
import org.sosy_lab.java_smt.solvers.opensmt.api.Model;
import org.sosy_lab.java_smt.solvers.opensmt.api.PTRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SRef;

public class OpenSmtEvaluator extends AbstractEvaluator<PTRef, SRef, Logic> {

  private final Model osmtModel;

  OpenSmtEvaluator(OpenSmtAbstractProver<?> pProver, OpenSmtFormulaCreator pCreator) {
    super(pProver, pCreator);
    osmtModel = pProver.getOsmtSolver().getModel();
  }

  @Override
  public PTRef evalImpl(PTRef f) {
    Preconditions.checkState(!isClosed());
    return osmtModel.evaluate(f);
  }
}
