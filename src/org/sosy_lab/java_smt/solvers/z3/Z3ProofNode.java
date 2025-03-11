package org.sosy_lab.java_smt.solvers.z3;

import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.basicimpl.AbstractProofNode;

public class Z3ProofNode extends AbstractProofNode {

        public Z3ProofNode(Formula pFormula, ProofRule pProofRule) {
        super(pProofRule, pFormula);
        }
}