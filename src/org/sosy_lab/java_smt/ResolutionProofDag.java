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
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.basicimpl.AbstractProofDag;
import org.sosy_lab.java_smt.basicimpl.AbstractProofNode;

/**
 * This class represents a resolution proof DAG. Its nodes might be of the type {@link
 * AxiomProofNode} or {@link ResolutionProofNode}. It is used to represent proofs based on the
 * RESOLUTE proof format from SMTInterpol.
 *
 * @see ResProofRule
 */
@SuppressWarnings("all")
public class ResolutionProofDag extends AbstractProofDag {
  // Work in progress. The functionality of producing just nodes should be provided first.
  // The idea is to provide extended functionality (by providng a set of edges for example).

  /*
  public ResolutionProofDAG() {
    super();
  }


  public static ResolutionProofDAG fromTerm(
      Term proof, FormulaManager pManager,
      Map<String, BooleanFormula> pAnnotatedTerms) {

    // Use our new ProofTermParser to convert the proof term to a ResolutionProofDAG
    return ProofTermParser.convert(proof, pManager, pAnnotatedTerms);
  }

  private static void traverseTerm(Term term, ResolutionProofDAG dag, ProofNode parentClause) {
    if (term instanceof AnnotatedTerm) {
      AnnotatedTerm annotatedTerm = (AnnotatedTerm) term;
      for (Annotation annotation : annotatedTerm.getAnnotations()) {
        /*
        if (annotation.getKey().equals(ProofConstants.ANNOTKEY_PROVES)) {
          //ProofNode<ResAxiom> clause = annotation.getValue().toString();
          if (parentClause != null) {
            dag.addEdge(parentClause, clause);
          } else {
            dag.addNode(clause);
          }
          for (Term subTerm : annotatedTerm.getSubterms()) {
            traverseTerm(subTerm, dag, clause);
          }
        }


      }
    }
  }



  @Override
  public void addNode(ProofNode node) {
    super.addNode(node);
  }

  @Override
  public ProofNode getNode(int nodeId) {
    return super.getNode(nodeId);
  }

  @Override
  public void addEdge(int parentNodeId, int childNodeId) {
    super.addEdge(parentNodeId, childNodeId);
  }

   */

  public static class ResolutionProofNode extends AbstractProofNode implements ProofNode {

    private final Formula pivot;

    public ResolutionProofNode(Formula formula, Formula pivot) {
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

  public static class AxiomProofNode extends AbstractProofNode implements ProofNode {

    public AxiomProofNode(ResAxiom rule, Formula formula) {
      super(
          Objects.requireNonNull(rule, "Rule must not be null"),
          Objects.requireNonNull(formula, "Formula must not be null"));
    }

  }
}
