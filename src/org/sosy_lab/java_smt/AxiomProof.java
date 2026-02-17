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
import org.sosy_lab.java_smt.ResProofRule.ResAxiom;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.Proof;
import org.sosy_lab.java_smt.basicimpl.AbstractProof;

public class AxiomProof extends AbstractProof {

  public AxiomProof(ResAxiom rule, Formula formula) {
    super(
        Objects.requireNonNull(rule, "Rule must not be null"),
        Objects.requireNonNull(formula, "Formula must not be null"));
  }

  @Override
  protected void addChild(Proof pProof) {
    super.addChild(pProof);
  }
}
