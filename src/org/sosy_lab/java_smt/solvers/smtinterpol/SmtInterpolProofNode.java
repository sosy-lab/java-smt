/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.smtinterpol;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.util.Locale;
import java.util.Optional;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.api.proofs.SmtInterpolProofNodeAnnotation;
import org.sosy_lab.java_smt.api.proofs.SmtInterpolProofNodeExtension;
import org.sosy_lab.java_smt.basicimpl.AbstractProofNode;

/**
 * This class represents a SMTInterpol proof DAG in the JavaSMT proof interface.
 *
 * <p>Many formulas that are not in the leafs or are pivots for resolution are null, as SMTInterpol
 * does not provide them. Every resolution node has 3 children: sub-proof, pivot, sub-proof. There
 * exists the RUP sub-proof, meaning that the stored formula was proven by applying RUP to the child
 * of the node. The PIVOT and RUP proof rules have been added to the proof format from SMTInterpol
 * for the sake of offering a proof rule at every step of the proof as well as allowing to display
 * the pivots for resolution steps.
 */
class SmtInterpolProofNode extends AbstractProofNode implements SmtInterpolProofNodeExtension {

  /** SMTInterpol-specific proof rules. */
  enum Rules implements ProofRule {
    COEFFS("coeffs"),
    VALUES("values"),
    DIVISOR("divisor"),
    POS("pos"),
    UNIT("unit"),
    DEFINE_FUN("define-fun"),
    DECLARE_FUN("declare-fun"),
    RUP("rup"),
    PIVOT("pivot");

    private final String name;

    Rules(String pName) {
      name = pName;
    }

    @Override
    public String getName() {
      return name;
    }

    static Rules getFromName(String pName) {
      String upperName = pName.toUpperCase(Locale.ENGLISH);
      if (upperName.equals("DEFINE-FUN")) {
        return DEFINE_FUN;
      } else if (upperName.equals("DECLARE-FUN")) {
        return DECLARE_FUN;
      }
      try {
        return Rules.valueOf(upperName);
      } catch (IllegalArgumentException e) {
        return null;
      }
    }
  }

  private final ImmutableList<SmtInterpolProofNodeAnnotation> annotations;

  SmtInterpolProofNode(
      ProofRule pRule,
      Formula pFormula,
      ImmutableList<SmtInterpolProofNodeAnnotation> pAnnotations) {
    super(Optional.ofNullable(pRule), pFormula);
    this.annotations = Preconditions.checkNotNull(pAnnotations);
  }

  SmtInterpolProofNode(ProofRule pRule, Formula pFormula) {
    this(pRule, pFormula, ImmutableList.of());
  }

  @Override
  protected void addChild(ProofNode pProof) {
    super.addChild(pProof);
  }

  @Override
  public ImmutableList<SmtInterpolProofNodeAnnotation> getAnnotations() {
    return annotations;
  }

  @Override
  public String proofAsString() {
    return super.proofAsString();
  }
}
