/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.smtinterpol;

import java.util.Locale;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.Proof;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.basicimpl.AbstractProof;

/**
 * This class represents a SMTInterpol proof DAG in the JavaSMT proof interface. Many formulas that
 * are not in the leafs or are pivots for resolution are null, as SMTInterpol does not provide them.
 * Every resolution node has 3 chilren: sub-proof, pivot, sub-proof. There exists the RUP sub-proof,
 * these means that the stored formula was proven by applying RUP to the child of the node. The
 * PIVOT and RUP proof rules have been added to the proof format from SMTInterpol for the sake of
 * offering a proof rule at every step of the proof as well as allowing to display the pivots for
 * resolution steps.
 */
class SmtInterpolProof extends AbstractProof {
  protected enum Rules implements ProofRule {
    COEFFS("coeffs"),
    VALUES("values"),
    DIVISOR("divisor"),
    POS("pos"),
    UNIT("unit"),
    DEFINE_FUN("define-fun"),
    DECLARE_FUN("declare-fun"),
    RUP("rup"),
    PIVOT("pivot");
    final String name;

    Rules(String pDefineFun) {
      name = pDefineFun;
    }

    static Rules getFromName(String pName) {
      if (pName.equals("DEFINE-FUN")) {
        return DEFINE_FUN;
      } else if (pName.equals("DECLARE-FUN")) {
        return DECLARE_FUN;
      }
      return Rules.valueOf(pName);
    }

    @Override
    public String getName() {
      if (this.equals(DEFINE_FUN) || this.equals(DECLARE_FUN)) {
        return name;
      } else {
        return name().toLowerCase(Locale.ENGLISH);
      }
    }
  }

  SmtInterpolProof(ProofRule pRule, Formula pFormula) {
    super(pRule, pFormula);
  }

  @Override
  protected void addChild(Proof pProof) {
    super.addChild(pProof);
  }

  @Override
  public String proofAsString() {
    return super.proofAsString();
  }
}
