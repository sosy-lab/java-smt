/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.princess;


import ap.proof.certificates.BranchInference;
import ap.proof.certificates.BranchInferenceCertificate;
import ap.proof.certificates.Certificate;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.ProofFrame;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.basicimpl.AbstractProof;
import scala.collection.immutable.Seq;

public final class PrincessProof extends AbstractProof {
  private static class Frame extends ProofFrame<Certificate> {
    protected Frame(Certificate proof) {
      super(proof);
    }
  }

  private final List<PrincessProof> children = new ArrayList<>();

  public PrincessProof(ProofRule pRule, Formula pFormula) {
    super(pRule, pFormula);
  }

  public static PrincessProof buildProofDAG(Certificate root, PrincessFormulaCreator creator) {
    Deque<Frame> stack = new ArrayDeque<>();

    Map<Certificate, PrincessProof> computed = new IdentityHashMap<>();

    stack.push(new Frame(root));

    while (!stack.isEmpty()) {
      Frame frame = stack.peek();

      if (!frame.isVisited()) {
        // Preprocessing step: mark visited and compute number of children (args)
        Seq<Certificate> subs = (Seq<Certificate>) frame.getProof().subCertificates();
        List<Certificate> children = scala.jdk.javaapi.CollectionConverters.asJava(subs);
        frame.setNumArgs(children.size());
        frame.setAsVisited(true);

        for (int i = children.size() - 1; i >= 0; i--) {
          Certificate child = children.get(i);
          if (!computed.containsKey(child)) {
            stack.push(new Frame(child));
          }
        }
      } else {

        stack.pop();
        int numArgs = frame.getNumArgs();
        Certificate cert = frame.getProof();
        PrincessProof node = generateProof(cert, creator);

        Seq<Certificate> subs = (Seq<Certificate>) cert.subCertificates();
        List<Certificate> children = scala.jdk.javaapi.CollectionConverters.asJava(subs);

        for (Certificate c : children) {
          PrincessProof childNode = computed.get(c);
          if (childNode != null) {
            node.addChild(childNode);
          }
        }

        computed.put(cert, node);
      }
    }

    return computed.get(root);
  }

  private static PrincessProof generateProof(Certificate cert, PrincessFormulaCreator creator) {;
    PrincessProof rule = handleProofCase(cert, creator);
    return rule;
  }

  public static PrincessProof handleProofCase(Certificate cert, PrincessFormulaCreator creator) {
    String name = toUpperSnake(cert.getClass().getSimpleName());
    PrincessProofRule.Certificate certType = PrincessProofRule.Certificate.valueOf(name);
    switch (certType) {
      case BETA_CERTIFICATE:

        throw new UnsupportedOperationException("Not implemented yet");
      case BINARY_CERTIFICATE:
        throw new UnsupportedOperationException("Not implemented yet");
      case BRANCH_INFERENCE_CERTIFICATE:
        return handleBranchInferenceCertificate(cert, creator);
      case CLOSE_CERTIFICATE:
        throw new UnsupportedOperationException("Not implemented yet");

      case CUT_CERTIFICATE:
        throw new UnsupportedOperationException("Not implemented yet");

      case OMEGA_CERTIFICATE:
        throw new UnsupportedOperationException("Not implemented yet");

      case PARTIAL_CERTIFICATE:
        throw new UnsupportedOperationException("Not implemented yet");

      case SPLIT_EQ_CERTIFICATE:
        throw new UnsupportedOperationException("Not implemented yet");

      case STRENGTHEN_CERTIFICATE:
        throw new UnsupportedOperationException("Not implemented yet");

      default:
        throw new IllegalArgumentException("Unknown proof certificate: " + name);
    }
  }

  public static PrincessProof handleBranchInferenceCertificate(
      Certificate cert,
      PrincessFormulaCreator creator) {
    BranchInferenceCertificate bic = (BranchInferenceCertificate) cert;
    List<? extends BranchInference> inferences = scala.jdk.javaapi.CollectionConverters.asJava(bic.inferences());
    if (!inferences.isEmpty()) {
      for (BranchInference inf : inferences) {
        String name = toUpperSnake(inf.getClass().getSimpleName());
        PrincessProofRule.Inference infType = PrincessProofRule.Inference.valueOf(name);
        switch (infType) {
          case ALPHA_INFERENCE:
            throw new UnsupportedOperationException("Not implemented yet");

          case ANTI_SYMMETRY_INFERENCE:
            throw new UnsupportedOperationException("Not implemented yet");

          case COLUMN_REDUCE_INFERENCE:
            throw new UnsupportedOperationException("Not implemented yet");

          case COMBINE_EQUATIONS_INFERENCE:
            throw new UnsupportedOperationException("Not implemented yet");

          case COMBINE_INEQUALITIES_INFERENCE:
            throw new UnsupportedOperationException("Not implemented yet");

          case DIRECT_STRENGTHEN_INFERENCE:
            throw new UnsupportedOperationException("Not implemented yet");

          case DIV_RIGHT_INFERENCE:
            throw new UnsupportedOperationException("Not implemented yet");

          case GROUND_INST_INFERENCE:
            throw new UnsupportedOperationException("Not implemented yet");

          case MACRO_INFERENCE:
            throw new UnsupportedOperationException("Not implemented yet");

          case PARTIAL_CERTIFICATE_INFERENCE:
            throw new UnsupportedOperationException("Not implemented yet");

          case PRED_UNIFY_INFERENCE:
            throw new UnsupportedOperationException("Not implemented yet");

          case QUANTIFIER_INFERENCE:
            throw new UnsupportedOperationException("Not implemented yet");

          case REDUCE_INFERENCE:
            throw new UnsupportedOperationException("Not implemented yet");

          case REDUCE_PRED_INFERENCE:
            throw new UnsupportedOperationException("Not implemented yet");

          case SIMP_INFERENCE:
            throw new UnsupportedOperationException("Not implemented yet");

          case THEORY_AXIOM_INFERENCE:
            throw new UnsupportedOperationException("Not implemented yet");

          default:
            throw new IllegalArgumentException("Unknown proof inference: " + name);
        }
      }
    }
   throw new UnsupportedOperationException("Not implemented yet");
  }

  public static String toUpperSnake(String s) {
    return s.replaceAll("([a-z])([A-Z])", "$1_$2")
        .replaceAll("([A-Z]+)([A-Z][a-z])", "$1_$2")
        .toUpperCase();
  }
}
