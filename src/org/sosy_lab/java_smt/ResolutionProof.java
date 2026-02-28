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
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.basicimpl.AbstractProof;

/**
 * This class represents a resolution proof DAG. Its nodes might be of the type {@link AxiomProof}
 * or {@link ResolutionProof}. It is used to represent proofs based on the RESOLUTE proof format
 * from SMTInterpol.
 *
 * @see ResProofRule
 */
public class ResolutionProof extends AbstractProof {
  // Work in progress. The functionality of producing just nodes should be provided first.
  // The idea is to provide extended functionality (by providng a set of edges for example).

  private final Formula pivot;

  @Override
  public void addChild(Proof pProof) {
    super.addChild(pProof);
  }

  public ResolutionProof(Formula formula, Formula pivot) {
    super(ResAxiom.RESOLUTION, Objects.requireNonNull(formula, "Formula must not be null"));
    this.pivot = Objects.requireNonNull(pivot, "Pivot must not be null");
  }

  public Formula getPivot() {
    return pivot;
  }

  @Override
  public ProofRule getRule() {
    return super.getRule();
  }
}
