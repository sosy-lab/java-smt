/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.smtinterpol;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofRules;

import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.EQAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantAnnotation;
import java.util.Map;
import org.sosy_lab.java_smt.ResProofRule;
import org.sosy_lab.java_smt.ResProofRule.ResAxiom;
import org.sosy_lab.java_smt.ResolutionProofDAG;
import org.sosy_lab.java_smt.ResolutionProofNode;
import org.sosy_lab.java_smt.SourceProofNode;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.basicimpl.AbstractProofNode;


class SmtInterpolProofNode extends AbstractProofNode<String> {
  static class ResolutionProofDAGBuilder {
    private final SmtInterpolFormulaCreator creator;
    private Theory theory;

    public ResolutionProofDAGBuilder(SmtInterpolFormulaCreator creator) {
      this.creator = creator;
    }

    /*
    // Morris traversal that processes every node and returns the created ResolutionProofDAG.
    public static ResolutionProofDAG buildDag(SmtInterpolProofNode root) {
      SmtInterpolProofNode current = root;
      // Morris Traversal: process each node in inorder without extra stack.
      while (current != null) {
        if (current.getLeft() == null) {
          current.processNode();
          current = current.getRight();
        } else {
          SmtInterpolProofNode predecessor = current.getLeft();
          while (predecessor.getRight() != null && predecessor.getRight() != current) {
            predecessor = predecessor.getRight();
          }
          if (predecessor.getRight() == null) {
            predecessor.setRight(current); // create temporary thread
            current = current.getLeft();
          } else {
            predecessor.setRight(null); // remove the thread
            current = current.getRight();
          }
        }
      }
      // Create DAG from the processed tree.
      ResolutionProofDAG dag = new ResolutionProofDAG();
      addDagEdges(root, dag);
      return dag;
    }
     */

    // Recursively adds nodes and edges from the tree to the dag.
    private static void addDagEdges(SmtInterpolProofNode node, ResolutionProofDAG dag) {
      if (node == null) {
        return;
      }
      dag.addNode(node.getTransformed());
      if (node.getLeft() != null) {
        dag.addEdge(node.getTransformed(), node.getLeft().getTransformed());
        addDagEdges(node.getLeft(), dag);
      }
      if (node.getRight() != null) {
        dag.addEdge(node.getTransformed(), node.getRight().getTransformed());
        addDagEdges(node.getRight(), dag);
      }
    }

    public void processResNode(SmtInterpolProofNode node) {
      if (node.getLeft() == null && node.getRight() == null) {
        throw new UnsupportedOperationException("Cannot process leaf node");
      } else {
        ResolutionNode rn = (ResolutionNode) node.node;
        Antecedent[] antecedents = rn.getAntecedents();
        Literal pivot = antecedents[0].mPivot;
        node.transformed = new ResolutionProofNode(node.getFormula(),
            creator.encapsulateBoolean(pivot.getSMTFormula(theory)));
      }
    }

    /*
    public void processSourceNode(SmtInterpolProofNode node) {
      if (node.getLeft() == null && node.getRight() == null) {
        node.transformed = new SourceProofNode(node.getFormula());
      } else {
        throw new UnsupportedOperationException("Cannot process resolution node");
      }
    }
     */
  }

  private static ProofNode node;
  private SmtInterpolProofNode left;
  private SmtInterpolProofNode right;
  private org.sosy_lab.java_smt.api.proofs.ProofNode transformed;


  protected SmtInterpolProofNode(String rule, Formula formula) {
    super(rule, formula);
  }

  /*
  public static SmtInterpolProofNode create(
      Clause pClause, Theory pTheory,
      Map<String, BooleanFormula> pAnnotatedTerms, SmtInterpolFormulaCreator pCreator) {
    Term clsAsTerm = pClause.toTerm(pTheory);
    boolean createFormula = true;
    String termName = null;
    ProofNode pn = pClause.getProof();
    SmtInterpolProofNode newNode;
    String rule;
    if (clsAsTerm instanceof AnnotatedTerm) {
      termName = getTermName((AnnotatedTerm) clsAsTerm);
      if (termName != null) {
        createFormula = false;
      }
    }

    if (!pn.isLeaf()) {
      rule = ProofRules.RES;
      newNode = new SmtInterpolProofNode(rule,
          createFormula ? pCreator.encapsulateBoolean(clsAsTerm) : pAnnotatedTerms.get(termName));
      newNode.setProofNode(pn);
      ResolutionNode rn = (ResolutionNode) pn;
      newNode.left = create(rn.getPrimary(), pTheory, pAnnotatedTerms, pCreator);
      Antecedent[] antecedents = rn.getAntecedents();
      if (antecedents.length > 0) {
        newNode.right = create(antecedents[0].mAntecedent, pTheory, pAnnotatedTerms, pCreator);
      }
    } else {
      LeafNode ln = (LeafNode) pn;
      Term res;
      final IAnnotation annot = ln.getTheoryAnnotation();
      if (ln.getLeafKind() == -1) {
        rule = "INPUT";
      } else if (ln.getLeafKind() >= 0) {
        rule = "TAUTOLOGY";
      }
      if (annot == null) {
        assert ln.getLeafKind() == LeafNode.ASSUMPTION;
        rule = ProofRules.ASSUME;

      } else if (annot instanceof EQAnnotation) {
        rule = ProofRules.ORACLE;

      } else if (annot instanceof LAAnnotation) {
        rule =
      } else if (annot instanceof CCAnnotation) {
        rule =
      } else if (annot instanceof QuantAnnotation) {
        rule =
      } else if (annot instanceof SourceAnnotation) {
        rule =
      }
      newNode = new SmtInterpolProofNode(rule,
          createFormula ? pCreator.encapsulateBoolean(clsAsTerm) : pAnnotatedTerms.get(termName));
      newNode.setProofNode(pn);
    }


    return newNode;
  }
   */
  public org.sosy_lab.java_smt.api.proofs.ProofNode getTransformed() {
    return transformed;
  }

  public SmtInterpolProofNode getLeft() {
    return left;
  }

  public SmtInterpolProofNode getRight() {
    return right;
  }

  // Helper for assigning temporary thread pointers
  public void setRight(SmtInterpolProofNode node) {
    this.right = node;
  }

  private void setProofNode(ProofNode pNode) {
    this.node = pNode;
  }

  private static String getTermName(AnnotatedTerm pTerm) {
    for (Annotation annotation : pTerm.getAnnotations()) {
      if (annotation.getKey().equals(":named")) {
        return annotation.getValue().toString();
      }
    }
    return null;
  }

  private static ProofNode getNode() {
    return node;
  }

  public static Term annotationMethod(Clause cls, ProofRules rule) {
    ProofNode pn = cls.getProof();
    Term res = null;
    final IAnnotation annot = ((LeafNode) pn).getTheoryAnnotation();
    if (annot != null) {
      res = annot.toTerm(cls, rule);
    }
    return res;
  }

  /*



  public static ResolutionProofDAG generateProofDAG(ProofNode node) {
    ResolutionProofDAG dag = new ResolutionProofDAG();
    if (node == null) {
      return dag;
    }
    if (node.isLeaf()) {

    } else {
      ResolutionNode resNode = (ResolutionNode) node;
      ResolutionNode.Antecedent[] antecedents = resNode.getAntecedents();
      if (antecedents != null) {
        for (ResolutionNode.Antecedent antecedent : antecedents) {
          traverse(antecedent.mAntecedent.getProof());
        }
      }
    }
  }


  private void predecessorSetRight(SmtInterpolProofNode predecessor, SmtInterpolProofNode thread) {
    try {
      Field rightField = BinaryProofNode.class.getDeclaredField("right");
      rightField.setAccessible(true);
      rightField.set(predecessor, thread);
    } catch (Exception e) {
      throw new RuntimeException("Unable to set right field via reflection", e);
    }
  }

   */

}
