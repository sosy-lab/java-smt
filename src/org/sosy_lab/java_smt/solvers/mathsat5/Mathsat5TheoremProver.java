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
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;
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
    context.getFormulaManager().getBooleanFormulaManager();
    ProofNode result = pn;
    // ProofNode result = clausifyResChain(pn, context.getFormulaManager()
    // .getBooleanFormulaManager());
    msat_destroy_proof_manager(pm);

    return result;

    // return getProof0();
  }

  private ProofNode clausifyResChain(ProofNode proof, BooleanFormulaManager bfmgr) {
    BooleanFormulaVisitor<TraversalProcess> extractor =
        new BooleanFormulaVisitor<>() {
          List<BooleanFormula> andList = new ArrayList<>();
          List<BooleanFormula> orList = new ArrayList<>();

          @Override
          public TraversalProcess visitConstant(boolean value) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitBoundVar(BooleanFormula var, int deBruijnIdx) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitNot(BooleanFormula operand) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitAnd(List<BooleanFormula> operands) {
            andList.addAll(operands);
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitOr(List<BooleanFormula> operands) {
            orList.addAll(operands);
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitXor(BooleanFormula operand1, BooleanFormula operand2) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitEquivalence(
              BooleanFormula operand1, BooleanFormula operand2) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitImplication(
              BooleanFormula operand1, BooleanFormula operand2) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitIfThenElse(
              BooleanFormula condition, BooleanFormula thenFormula, BooleanFormula elseFormula) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitQuantifier(
              Quantifier quantifier,
              BooleanFormula quantifiedAST,
              List<Formula> boundVars,
              BooleanFormula body) {
            return TraversalProcess.CONTINUE;
          }

          @Override
          public TraversalProcess visitAtom(
              BooleanFormula atom, FunctionDeclaration<BooleanFormula> funcDecl) {
            return TraversalProcess.CONTINUE;
          }
        };
    return null;
  }

  protected ProofNode getProof0() {
    var proofFactory =
        new ProofFactory<Long>(this, "MATHSAT5") {
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
