/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.api.proofs.visitors;

import org.sosy_lab.java_smt.api.proofs.ProofDAG;
import org.sosy_lab.java_smt.api.proofs.ProofNode;

public interface ProofVisitor<R> {
  void visitNode(ProofNode<R> node);
  void visitDAG(ProofDAG<R> dag);
}
