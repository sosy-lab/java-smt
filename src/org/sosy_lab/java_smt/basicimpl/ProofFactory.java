/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.basicimpl;

import org.sosy_lab.java_smt.ResProofRule.ResAxiom;
import org.sosy_lab.java_smt.ResolutionProofDag.AxiomProofNode;
import org.sosy_lab.java_smt.ResolutionProofDag.ResolutionProofNode;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5ProofNode;

/**
 * A factory for creating proof nodes. The methods of this class are to be used in the ProofNode
 * implementations of each solver to be able to convert the proof object given back by the solver to
 * a proof in JavaSMT.
 *
 * @param <T> The type of the proof object.
 */
public class ProofFactory<T> {

  //private final FormulaCreator<?, ?, ?, ?> formulaCreator;
  private final ProverEnvironment prover;
  private final Solvers solver;

  enum Solvers {
    OPENSMT,
    MATHSAT5,
    SMTINTERPOL,
    Z3,
    PRINCESS,
    BOOLECTOR,
    CVC4,
    CVC5,
    YICES2,
    BITWUZLA
  }

  protected ProofFactory(ProverEnvironment pProver, String pSolver) {
    //formulaCreator = pCreator;
    prover = pProver;
    solver = Solvers.valueOf(pSolver);
  }

  protected ProofNode createProofNode(T proof) {
    return createProofNode0(proof);
  }

  protected ProofNode createProofNode0(T proof) {

    switch (solver) {
      case MATHSAT5:
        return Mathsat5ProofNode.fromMsatProof(prover, (long) proof);
      case CVC5:
        return null;
      default:
        throw new UnsupportedOperationException("Unsupported solver: " + solver);
    }
  }

  protected static ProofNode createSourceNode(ResAxiom rule, Formula formula) {
    return new AxiomProofNode(rule, formula);
  }

  protected static ProofNode createResolutionNode(Formula formula, Formula pivot) {
    return new ResolutionProofNode(formula, pivot);
  }
}
