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
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.basicimpl.AbstractProof;

/**
 * This class represents a resolution proof DAG. Its nodes might be of the type {@link
 * AxiomSubproof} or {@link ResolutionSubproof}. It is used to represent proofs based on the
 * RESOLUTE proof format from SMTInterpol.
 *
 * @see ResProofRule
 */
public class ResolutionProof extends AbstractProof {
  // Work in progress. The functionality of producing just nodes should be provided first.
  // The idea is to provide extended functionality (by providng a set of edges for example).

  public static class ResolutionSubproof extends AbstractSubproof implements Subproof {

    private final Formula pivot;

    @Override
    public void addChild(Subproof pSubproof) {
      super.addChild(pSubproof);
    }

    public ResolutionSubproof(Formula formula, Formula pivot, AbstractProof p) {
      super(ResAxiom.RESOLUTION, Objects.requireNonNull(formula, "Formula must not be null"), p);
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

  public static class AxiomSubproof extends AbstractSubproof implements Subproof {

    public AxiomSubproof(ResAxiom rule, Formula formula, AbstractProof proof) {
      super(
          Objects.requireNonNull(rule, "Rule must not be null"),
          Objects.requireNonNull(formula, "Formula must not be null"),
          proof);
    }

    @Override
    protected void addChild(Subproof pSubproof) {
      super.addChild(pSubproof);
    }
  }
}
