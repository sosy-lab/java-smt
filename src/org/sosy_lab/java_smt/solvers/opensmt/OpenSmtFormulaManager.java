// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import opensmt.OpenSmt;
import opensmt.PTRef;
import opensmt.SRef;
import opensmt.SymRef;
import org.sosy_lab.common.Appender;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.basicimpl.AbstractFormulaManager;

class OpenSmtFormulaManager extends AbstractFormulaManager<PTRef, SRef, OpenSmt, SymRef> {
  OpenSmtFormulaManager(
      OpenSmtFormulaCreator pFormulaCreator,
      OpenSmtUFManager pFfmgr,
      OpenSmtBooleanFormulaManager pBfmgr,
      OpenSmtIntegerFormulaManager pIfmgr,
      // OpenSmtRationalFormulaManager pRfmgr,
      OpenSmtArrayFormulaManager pAfmgr) {
    super(
        pFormulaCreator,
        pFfmgr,
        pBfmgr,
        pIfmgr,
        null, // pRfmgr,
        null, // pBvfmgr,
        null, // pFpfmgr,
        null, // pQfmgr,
        pAfmgr,
        null, // pSLfmgr,
        null); // pStrmgr);
  }

  @Override
  public BooleanFormula parse(String pS) throws IllegalArgumentException {
    // FIXME
    throw new UnsupportedOperationException();
  }

  @Override
  public Appender dumpFormula(PTRef f) {
    // FIXME
    throw new UnsupportedOperationException();
  }
}
