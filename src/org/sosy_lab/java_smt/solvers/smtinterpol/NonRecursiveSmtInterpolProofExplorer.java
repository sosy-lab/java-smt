/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2026 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.smtinterpol;

import com.google.common.collect.ImmutableList;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.java_smt.solvers.smtinterpol.ResProofRule.ResAxiom;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.api.proofs.SmtInterpolProofNodeAnnotation;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import org.sosy_lab.java_smt.solvers.smtinterpol.SmtInterpolProofNode.Rules;

/**
 * Non-recursive explorer for SMTInterpol RESOLUTE proof format.
 *
 * <p>This class transforms the proof term returned by SMTInterpol into a proof DAG suitable for the
 * JavaSMT proof API. It uses an iterative DFS approach to avoid stack overflow on large proofs.
 * Based on the original recursive ProofTermParser implementation.
 */
class NonRecursiveSmtInterpolProofExplorer {

  private final FormulaCreator<Term, ?, ?, ?> formulaCreator;
  private final Map<Term, SmtInterpolProofNode> termToNode = new HashMap<>();

  NonRecursiveSmtInterpolProofExplorer(FormulaCreator<Term, ?, ?, ?> pCreator) {
    formulaCreator = pCreator;
  }

  /**
   * Creates a proof DAG from the given proof term.
   *
   * @param proofTerm the proof term from SMTInterpol
   * @return the root node of the proof DAG
   */
  SmtInterpolProofNode createProof(Term proofTerm) {
    if (termToNode.containsKey(proofTerm)) {
      return termToNode.get(proofTerm);
    }

    Deque<Frame> stack = new ArrayDeque<>();
    Map<Term, SmtInterpolProofNode> computed = new HashMap<>();

    stack.push(new Frame(proofTerm));

    while (!stack.isEmpty()) {
      Frame frame = stack.peek();

      if (!frame.isVisited()) {
        frame.setAsVisited();

        Term term = frame.getTerm();

        List<Term> children = getChildren(term);
        frame.setChildren(children);

        for (Term child : children) {
          if (!computed.containsKey(child) && !termToNode.containsKey(child)) {
            stack.push(new Frame(child));
          }
        }
      } else {
        stack.pop();

        SmtInterpolProofNode node = createNode(frame, computed);
        computed.put(frame.getTerm(), node);
        termToNode.put(frame.getTerm(), node);
      }
    }

    return computed.get(proofTerm);
  }

  /**
   * Extracts the children of a proof term.
   * - RESOLUTION: 3 children (pivot, leftProof, rightProof)
   * - AXIOM-based rules (DEL, EQUAL_NEGATIVE2, etc.): NO children (leaf)
   * - Other rules: may have children based on their structure
   *
   * @param term the term to extract children from
   * @return list of child terms
   */
  private List<Term> getChildren(Term term) {
    List<Term> children = new ArrayList<>();

    if (term instanceof ApplicationTerm) {
      ApplicationTerm app = (ApplicationTerm) term;
      String funcName = app.getFunction().getName();
      Term[] params = app.getParameters();

      if (funcName.equals("..res") && params.length >= 3) {
        // RESOLUTION: params[0] = pivot formula, params[1] = left proof, params[2] = right proof
        children.add(params[0]);  // Pivot (will be wrapped as PIVOT node)
        children.add(params[1]);  // Left proof
        children.add(params[2]);  // Right proof
      } else if (funcName.equals("..res") && params.length == 2) {
        // Two-parameter RESOLUTION: params[0] = pivot, params[1] = proof
        children.add(params[0]);
        children.add(params[1]);
      } else if (funcName.equals("..res") && params.length == 1) {
        // Single-parameter RESOLUTION: just the pivot
        children.add(params[0]);
      } else if (funcName.equals("let")) {
        // Let binding: extract the body as child
        if (params.length >= 2 && params[params.length - 1] instanceof ApplicationTerm) {
          children.add(params[params.length - 1]);
        }
      }

    } else if (term instanceof AnnotatedTerm) {
      AnnotatedTerm annotated = (AnnotatedTerm) term;
      Term subterm = annotated.getSubterm();

      // Check if this is an AXIOM-based rule (DEL, EQUAL_NEGATIVE2, NOT-, OR+, etc.)
      boolean isAxiomRule = false;
      for (Annotation ann : annotated.getAnnotations()) {
        String key = ann.getKey();
        if (key.equals(":del!") || key.equals(":=-1") || key.equals(":=+1") 
            || key.equals(":=+2") || key.equals(":=-2") || key.equals(":not-") 
            || key.equals(":not+") || key.equals(":or-") || key.equals(":or+")
            || key.equals(":and-") || key.equals(":and+") || key.equals(":=+") 
            || key.equals(":=-") || key.equals(":=+1") || key.equals(":=-1")) {
          isAxiomRule = true;
          break;
        }
      }

      if (isAxiomRule) {
        // AXIOM-based rules are LEAVES, return empty list
        return children;
      }

      // If subterm is RESOLUTION, extract its params as children
      if (subterm instanceof ApplicationTerm) {
        ApplicationTerm subApp = (ApplicationTerm) subterm;
        if (subApp.getFunction().getName().equals("..res")) {
          Term[] params = subApp.getParameters();
          // Add all RESOLUTION parameters as children
          for (Term param : params) {
            children.add(param);
          }
        } else {
          children.add(subterm);
        }
      } else {
        children.add(subterm);
      }
    }

    return children;
  }

  /**
   * Creates a proof node from the processed frame.
   *
   * @param frame the processed frame
   * @param computed the map of already computed nodes
   * @return the created proof node
   */
  private SmtInterpolProofNode createNode(
      Frame frame, Map<Term, SmtInterpolProofNode> computed) {

    Term term = frame.getTerm();
    List<Term> childTerms = frame.getChildren();

    ImmutableList.Builder<SmtInterpolProofNodeAnnotation> annotationsBuilder =
        ImmutableList.builder();

    ProofRule rule = null;
    Formula formula = null;

    if (term instanceof ApplicationTerm) {
      // Pure ApplicationTerm, rule comes from function name
      ApplicationTerm app = (ApplicationTerm) term;
      String funcName = app.getFunction().getName();
      Term[] params = app.getParameters();

      if (funcName.equals("..res") && params.length >= 3) {
        rule = ResAxiom.RESOLUTION;
        // Pivot is handled as a child node, not an annotation
        // Formula stays null for RESOLUTION

      } else if (funcName.equals("..assume") && params.length > 0) {
        rule = ResAxiom.ASSUME;
        // Store the assumed term as formula
        Term assumedTerm = params[0];
        if (assumedTerm instanceof AnnotatedTerm) {
          assumedTerm = ((AnnotatedTerm) assumedTerm).getSubterm();
        }
        formula = encapsulateFormula(assumedTerm);

      } else if (funcName.equals("..axiom")) {
        // Pure axiom - rule comes from the function name
        rule = ResAxiom.RESOLUTION;
      }

    } else if (term instanceof AnnotatedTerm) {
      // Annotated term - first extract the rule from the subterm, then store annotations
      AnnotatedTerm annotated = (AnnotatedTerm) term;
      Term subterm = annotated.getSubterm();

      // Step 1: Extract rule from subterm (ApplicationTerm)
      if (subterm instanceof ApplicationTerm) {
        ApplicationTerm subApp = (ApplicationTerm) subterm;
        String subFuncName = subApp.getFunction().getName();
        Term[] subParams = subApp.getParameters();

        if (subFuncName.equals("..res") && subParams.length >= 3) {
          rule = ResAxiom.RESOLUTION;
          // Pivot is handled as a child node, not an annotation
          // Formula stays null for RESOLUTION

        } else if (subFuncName.equals("..assume") && subParams.length > 0) {
          rule = ResAxiom.ASSUME;
          Term assumedTerm = subParams[0];
          if (assumedTerm instanceof AnnotatedTerm) {
            assumedTerm = ((AnnotatedTerm) assumedTerm).getSubterm();
          }
          formula = encapsulateFormula(assumedTerm);

        } else if (subFuncName.equals("..axiom")) {
          rule = ResAxiom.RESOLUTION;
        }
      }

      // Step 2: Store all annotations (metadata about the node)
      for (Annotation ann : annotated.getAnnotations()) {
        String key = ann.getKey();
        Object value = ann.getValue();

        // :rup is metadata, not the rule
        if (key.equals(":rup")) {
          annotationsBuilder.add(SmtInterpolProofNodeAnnotationFactory.create(key, null));

        } else if (key.equals(":proves")) {
          parseProvesAnnotation(annotationsBuilder, value);

        } else if (key.equals(":named")) {
          annotationsBuilder.add(
              SmtInterpolProofNodeAnnotationFactory.create(key, value));

        } else if (key.equals(":input")) {
          annotationsBuilder.add(
              SmtInterpolProofNodeAnnotationFactory.create(key, value));

        } else if (key.equals(":del!") || key.startsWith(":")) {
          // Extract axiom rule from annotation key if applicable
          String axiomName = key.substring(1);
          ResAxiom axiom = ResProofRule.getFromName(axiomName);
          if (axiom != null) {
            rule = axiom;
          }
          annotationsBuilder.add(
              SmtInterpolProofNodeAnnotationFactory.create(key, value));
        }
      }
    }

    ImmutableList<SmtInterpolProofNodeAnnotation> annotations = annotationsBuilder.build();

    SmtInterpolProofNode node = new SmtInterpolProofNode(rule, formula, annotations);

    boolean isResolution = isResolutionNode(term);
    boolean hasSubtermResolution = term instanceof AnnotatedTerm 
        && isResolutionNode(((AnnotatedTerm) term).getSubterm());

    if (isResolution || hasSubtermResolution) {
      // RESOLUTION node: always has 3 children
      // childTerms[0] = pivot formula, childTerms[1] = left proof, childTerms[2] = right proof
      if (childTerms.size() >= 3) {
        Term pivotTerm = childTerms.get(0);
        Term leftTerm = childTerms.get(1);
        Term rightTerm = childTerms.get(2);

        // PIVOT formula comes DIRECTLY from pivotTerm (not from computed node)
        Formula pivotFormula = encapsulateFormula(pivotTerm);
        SmtInterpolProofNode pivotNode = new SmtInterpolProofNode(Rules.PIVOT, pivotFormula, ImmutableList.of());
        node.addChild(pivotNode);

        // Left and right proofs come from computed map
        SmtInterpolProofNode leftNode = computed.get(leftTerm);
        SmtInterpolProofNode rightNode = computed.get(rightTerm);
        if (leftNode != null) {
          node.addChild(leftNode);
        }
        if (rightNode != null) {
          node.addChild(rightNode);
        }
      } else if (childTerms.size() == 2) {
        // Two-parameter RESOLUTION
        Term pivotTerm = childTerms.get(0);
        Term proofTerm = childTerms.get(1);

        Formula pivotFormula = encapsulateFormula(pivotTerm);
        SmtInterpolProofNode pivotNode = new SmtInterpolProofNode(Rules.PIVOT, pivotFormula, ImmutableList.of());
        node.addChild(pivotNode);

        SmtInterpolProofNode proofNode = computed.get(proofTerm);
        if (proofNode != null) {
          node.addChild(proofNode);
        }
      } else if (childTerms.size() == 1) {
        // Single-parameter: just the child
        Term childTerm = childTerms.get(0);
        SmtInterpolProofNode childNode = computed.get(childTerm);
        if (childNode != null) {
          node.addChild(childNode);
        }
      }
    } else {
      // Non-RESOLUTION nodes: add children normally
      for (Term childTerm : childTerms) {
        SmtInterpolProofNode childNode = computed.get(childTerm);
        if (childNode != null) {
          node.addChild(childNode);
        }
      }
    }

    return node;
  }

  /**
   * Checks if a term represents a resolution node.
   *
   * @param term the term to check
   * @return true if the term is a resolution node
   */
  private boolean isResolutionNode(Term term) {
    if (term instanceof ApplicationTerm) {
      ApplicationTerm app = (ApplicationTerm) term;
      return app.getFunction().getName().equals("..res") && app.getParameters().length >= 3;
    }
    return false;
  }

  /**
   * Parses the :proves annotation value and adds it to the builder.
   * Deduplicates entries to avoid multiple :proves annotations with the same content.
   *
   * @param builder the annotation builder to add parsed annotations to
   * @param value the annotation value
   */
  private void parseProvesAnnotation(
      ImmutableList.Builder<SmtInterpolProofNodeAnnotation> builder, Object value) {
    if (!(value instanceof Object[])) {
      builder.add(SmtInterpolProofNodeAnnotationFactory.create(":proves", value));
      return;
    }

    Object[] values = (Object[]) value;

    // Deduplicate while preserving order
    List<Object> deduplicated = new ArrayList<>();
    Set<Object> seen = new HashSet<>();
    for (Object obj : values) {
      if (seen.add(obj)) {
        deduplicated.add(obj);
      }
    }

    // Add single :proves annotation with deduplicated array
    builder.add(
        SmtInterpolProofNodeAnnotationFactory.create(":proves", deduplicated.toArray()));
  }

  /**
   * Encapsulates a term as a Formula.
   *
   * @param term the term to encapsulate
   * @return the encapsulated formula, or null if encapsulation fails
   */
  private Formula encapsulateFormula(Term term) {
    if (term == null) {
      return null;
    }
    try {
      return formulaCreator.encapsulate(
          formulaCreator.getFormulaType(term), term);
    } catch (Exception e) {
      return null;
    }
  }

  /**
   * Frame for iterative DFS traversal.
   */
  private static class Frame {
    private final Term term;
    private List<Term> children = new ArrayList<>();
    private boolean visited = false;

    Frame(Term pTerm) {
      this.term = pTerm;
    }

    Term getTerm() {
      return term;
    }

    List<Term> getChildren() {
      return children;
    }

    void setChildren(List<Term> pChildren) {
      this.children = pChildren;
    }

    boolean isVisited() {
      return visited;
    }

    void setAsVisited() {
      this.visited = true;
    }
  }
}
