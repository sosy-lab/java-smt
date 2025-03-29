// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.mathsat5;

import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5FormulaManager.getMsatTerm;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_assert_formula;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_destroy_proof_manager;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_proof;
import static org.sosy_lab.java_smt.solvers.mathsat5.Mathsat5NativeApi.msat_get_proof_manager;

import com.google.common.base.Preconditions;
import java.util.Map;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.basicimpl.ProofFactory;

class Mathsat5TheoremProver extends Mathsat5AbstractProver<Void> implements ProverEnvironment {

  Mathsat5TheoremProver(
      Mathsat5SolverContext pMgr,
      ShutdownNotifier pShutdownNotifier,
      Mathsat5FormulaCreator creator,
      Set<ProverOptions> options) {
    super(pMgr, options, creator, pShutdownNotifier);
  }

  @Override
  protected void createConfig(Map<String, String> pConfig) {
    // nothing to do
  }

  @Override
  @Nullable
  protected Void addConstraintImpl(BooleanFormula constraint) throws InterruptedException {
    Preconditions.checkState(!closed);
    closeAllEvaluators();
    msat_assert_formula(curEnv, getMsatTerm(constraint));
    return null;
  }

  @Override
  public ProofNode getProof() throws SolverException, InterruptedException {
    Preconditions.checkState(!closed);
    Preconditions.checkState(this.isUnsat());

    ProofNode pn;
    long pm = msat_get_proof_manager(curEnv);
    long proof = msat_get_proof(pm);
    pn = Mathsat5ProofNode.fromMsatProof(this, proof);
    msat_destroy_proof_manager(pm);

    return pn;

    // return getProof0();
  }

  protected ProofNode getProof0() {
    var proofFactory =
        new ProofFactory<Long>(this.creator, this, "MATHSAT5") {
          public ProofNode createProofWrapper(long pProof) {
            return this.createProofNode(pProof);
          }
        };
    long pm = msat_get_proof_manager(curEnv);
    long proof = msat_get_proof(pm);
    ProofNode pn = proofFactory.createProofWrapper(proof);
    msat_destroy_proof_manager(pm);
    return pn;
  }
}
