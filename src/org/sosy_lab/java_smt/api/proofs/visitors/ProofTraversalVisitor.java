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

import java.util.HashSet;
import java.util.Set;
import org.sosy_lab.java_smt.api.proofs.ProofDag;
import org.sosy_lab.java_smt.api.proofs.ProofNode;

public class ProofTraversalVisitor implements ProofVisitor {
  private final Set<ProofNode> visited = new HashSet<>();

  @Override
  public void visitNode(ProofNode node) {
    if (visited.add(node)) {
      for (ProofNode child : node.getChildren()) {
        visitNode(child);
      }
    }
  }

  @Override
  public void visitDAG(ProofDag dag) {
    for (ProofNode node : dag.getNodes()) {
      if (!visited.contains(node)) {
        visitNode(node);
      }
    }
  }
}