/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt;

import java.util.Objects;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.basicimpl.AbstractProofNode;
import org.sosy_lab.java_smt.ResProofRule.ResAxiom;

public class ResolutionProofNode extends AbstractProofNode
    implements ProofNode {

  private final Formula pivot;

  public ResolutionProofNode(Formula formula, Formula pivot) {
    super(ResAxiom.RESOLUTION, Objects.requireNonNull(formula, "Formula must not be null"));
    this.pivot = Objects.requireNonNull(pivot, "Pivot must not be null");
  }



  @Override
  public boolean isSource() {
    return false;
  }

  public Formula getPivot() {
    return pivot;
  }

  @Override
  public ProofRule getRule() {
    return super.getRule();
  }
}
