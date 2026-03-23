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

import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.basicimpl.AbstractProof;

/**
 * Proof implementation for SMTInterpol.
 *
 * <p>This class wraps the proof DAG produced by SMTInterpol in the RESOLUTE proof format.
 */
public class SmtInterpolProof extends AbstractProof {

  public SmtInterpolProof(ProofNode pRoot) {
    super(pRoot);
  }
}
