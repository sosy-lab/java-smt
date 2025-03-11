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

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import java.util.Map;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.basicimpl.AbstractProofDAG;
import org.sosy_lab.java_smt.solvers.smtinterpol.ProofTermParser;

public class ResolutionProofDAG extends AbstractProofDAG {

  public ResolutionProofDAG() {
    super();
  }

  /**
   * Converts the proof Term returned from SMTInterpol into a ResolutionProofDAG.
   * This version traverses AnnotatedTerm instances looking for annotations with key
   * ProofConstants.ANNOTKEY_PROVES and uses the associated clause string.
   *
   * @param proof             the proof term
   * @return a ResolutionProofDAG representing the proof
   */
  public static ResolutionProofDAG fromTerm(
      Term proof, FormulaManager pManager,
      Map<String, BooleanFormula> pAnnotatedTerms) {

    // Use our new ProofTermParser to convert the proof term to a ResolutionProofDAG
    return ProofTermParser.convert(proof, pManager, pAnnotatedTerms);
  }

  /**
   * Recursively traverses the annotated proof term.
   *
   * @param term         the current term
   * @param dag          the proof DAG being constructed
   * @param parentClause the clause from the parent annotation (if available)
   */
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

         */
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
}
