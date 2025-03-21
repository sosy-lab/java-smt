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
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.basicimpl.AbstractProofNode;

public class SourceProofNode extends AbstractProofNode implements ProofNode {

  public SourceProofNode(ResAxiom rule, Formula formula) {
    super(
        Objects.requireNonNull(rule, "Rule must not be null"),
        Objects.requireNonNull(formula, "Formula must not be null"));
  }

  @Override
  public boolean isSource() {
    return true;
  }
}
