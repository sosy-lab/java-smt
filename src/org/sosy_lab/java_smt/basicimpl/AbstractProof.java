/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl;

import java.util.Objects;
import org.sosy_lab.java_smt.api.proofs.Proof;
import org.sosy_lab.java_smt.api.proofs.ProofNode;

public class AbstractProof implements Proof {
  public final ProofNode root;

  public AbstractProof(ProofNode pRoot) {
    root = Objects.requireNonNull(pRoot);
  }

  @Override
  public ProofNode getProofRoot() {
    return root;
  }
}
