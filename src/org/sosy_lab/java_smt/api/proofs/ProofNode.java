/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.api.proofs;


import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.visitors.ProofVisitor;

/**
 * A proof node in the proof DAG of a proof.
 *
 * @author Gabriel Carpio
 */
public interface ProofNode {
  List<ProofNode> getChildren();
  void addChild(ProofNode child);
  boolean isSource();
  boolean isSink();
  void accept(ProofVisitor visitor);
  Formula getFormula();
  int getId();
}
