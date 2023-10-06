// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import com.google.common.base.Preconditions;
import opensmt.Logic;
import opensmt.MainSolver;
import opensmt.Model;
import opensmt.PTRef;
import opensmt.SRef;
import org.sosy_lab.java_smt.basicimpl.AbstractEvaluator;

public class OpenSmtEvaluator extends AbstractEvaluator<PTRef, SRef, Logic> {

  private final MainSolver osmtSolver;
  private final Model osmtModel;

  OpenSmtEvaluator(OpenSmtAbstractProver<?> pProver, OpenSmtFormulaCreator pCreator) {
    super(pProver, pCreator);
    osmtSolver = pProver.getOsmtSolver();
    osmtModel = osmtSolver.getModel();
  }

  @Override
  public PTRef evalImpl(PTRef f) {
    Preconditions.checkState(!isClosed());
    return osmtModel.evaluate(f);
  }
}
