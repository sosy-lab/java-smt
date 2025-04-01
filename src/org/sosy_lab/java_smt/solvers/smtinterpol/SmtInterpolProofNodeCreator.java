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
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import org.sosy_lab.java_smt.ResProofRule;
import org.sosy_lab.java_smt.ResProofRule.ResAxiom;
import org.sosy_lab.java_smt.api.proofs.ProofFrame;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.proofs.ProofRule;

// SMTInterpol gives back a Term (apparently) only of instance ApplicationTerm or AnnotatedTerm,
// so the other instances are not needed.

@SuppressWarnings({"unchecked", "rawtypes", "unused", "static-access"})
class SmtInterpolProofNodeCreator {
  private final SmtInterpolFormulaCreator creator;
  private final SmtInterpolTheoremProver prover;
  private Map<Term, ProvitionalProofNode> computed = new ConcurrentHashMap<>();
  private Deque<SmtTermFrame> stack = new ArrayDeque<>();

  SmtInterpolProofNodeCreator(
      SmtInterpolFormulaCreator pCreator, SmtInterpolTheoremProver pProver) {
    creator = pCreator;
    prover = pProver;
  }

  private enum Rup implements ProofRule {
    RUP;

    @Override
    public String getName() {
      return "rup";
    }
  }

  private class SmtTermFrame extends ProofFrame<Term> {
    List<SmtTermFrame> children = new ArrayList<>();
    public SmtTermFrame(Term term) {
      super(term);
    }
  }

  ProofNode fromTerm(Term rootProof) {

    Deque<ProvitionalProofNode> stack = new ArrayDeque<>();

    Map<ProvitionalProofNode, ProofNode> computed = new HashMap<>();

    stack.push(new ProvitionalProofNode(rootProof));

    while (!stack.isEmpty()) {
      ProvitionalProofNode frame = stack.peek();

      if (!frame.isVisited) {


        frame.isVisited = true;
        // numChildren - 1 iterations
        for (int i = 10 - 1; i >= 0; i--) {
          // Proof child = rootProof.getChildren()[i];
          // !Computed.containsKey(child)
          if (true) {
            // stack.push(new Frame(child));
          }
        }
      } else {

        stack.pop();
        int numChildren = frame.children.size();

        // ProofRule proofRule =
        // new source node or resolution node
        for (int i = 0; i < numChildren - 1; i++) {
          // Proof child = frame.getProof().getChildren()[i];

          // if (computed.containsKey(child)) {
          if (true) {
            // pn.addChild(computed.get(child));
          }
        }
        // computed.put(frame.proof, pn);
      }
    }
    return computed.get(rootProof);
  }

  ProvitionalProofNode createPPNDag(Term proof) {
    try {
     ProvitionalProofNode root = new ProvitionalProofNode(proof);
     root.buildDag(proof);
     return root;
    } finally {
        stack.clear();
        computed.clear();
    }
  }

  class ProvitionalProofNode {
    Term pivot;
    ProofRule proofRule;
    List<Term> formulas = new ArrayList<>();
    boolean axiom;
    List<ProvitionalProofNode> children = new ArrayList<>();
    Term unprocessedTerm;
    boolean isVisited = false;

    public ProvitionalProofNode(Term pParameter) {
      this.unprocessedTerm = pParameter;
      //processTerm(pParameter);
    }

    void buildDag(Term term) {


      stack.push(new SmtTermFrame(term));

      while (!stack.isEmpty()) {
        SmtTermFrame frame = stack.peek();

        if (!frame.isVisited()) {
          frame.setAsVisited(true);
          processTerm(frame);
        } else {

          stack.pop();


                for (int i = 0; i < frame.children.size(); i++) {
                  Term child = frame.children.get(i).getProof();
                  ProvitionalProofNode childNode = computed.get(child);
                  this.children.add(childNode);
                }

        }
      }
    }

    void processTerm(SmtTermFrame frame) {
      Term pParameter = frame.getProof();

      if (pParameter instanceof ApplicationTerm) {
        processApplication(frame);
      } else if (pParameter instanceof AnnotatedTerm) {
        processAnnotated(frame);
      }
    }

    void processApplication(SmtTermFrame frame) {
      ApplicationTerm term = (ApplicationTerm) frame.getProof();
      Term[] parameters = term.getParameters();
      if (parameters.length == 3) {
        this.proofRule = ResAxiom.RESOLUTION;
        //This should be a resolution rule
        Term first = parameters[0];
        if (first instanceof AnnotatedTerm) {
          pivot = ((AnnotatedTerm) first).getSubterm();
        } else if (first instanceof ApplicationTerm) {
          pivot = first;
        }

        for (int i = parameters.length-1; i > 1; i--) {
          Sort sort = term.getSort();
          if (sort.toString().equals("..Proof")) {
              //children.add(new ProvitionalProofNode(parameters[i]));
              frame.setNumArgs(parameters.length-1);
              if (!computed.containsKey(parameters[i])) {
                SmtTermFrame childFrame = new SmtTermFrame(parameters[i]);
                stack.push(childFrame);
                frame.children.add(childFrame);
                //children.add(new ProvitionalProofNode(parameters[i]));
                computed.put(parameters[i], new ProvitionalProofNode(parameters[i]));
              }

          }
        }
      }

      if (term.getFunction().toString().contains("..assume")) {
        //This should be the assume axiom
        this.axiom = true;
        this.proofRule = ResAxiom.ASSUME;
        if (parameters[0] instanceof AnnotatedTerm) {
          this.formulas.add(((AnnotatedTerm) parameters[0]).getSubterm());
        } else {
          this.formulas.add(parameters[0]);
        }

      }

    }


    private void processAnnotated(SmtTermFrame frame) {
      AnnotatedTerm term = (AnnotatedTerm) frame.getProof();
      boolean rup = false;

      if (term.getSort().toString().equals("Bool")) {
        if (this.axiom) {
          this.pivot = term.getSubterm();
        } else {
          this.formulas.add(term.getSubterm());
        }
      }

      for (Annotation annotation : term.getAnnotations()) {
        ResAxiom rule;
        String key = annotation.getKey().substring(1);

        if (term.getSubterm().toString().equals("..axiom")) {
          this.axiom = true;
          // Annotation key should contain axiom name and value should contain an array with some
          // of its objects being Terms and the index before each one of those contains the
          // polarity.
          key = key.startsWith(":") ? key.substring(1) : key;

          rule = ResProofRule.getFromName(key);

          this.proofRule = rule;
          // This Annotation's value should have an array with the polarities and Terms that are
          // proven. This is the clause proven the ApplicationTerm. The array is empty for the
          // very first Term.
          // Now we need to go through the array and find the Term objects and their polarity.
          // This is the same for proves.
          if (annotation.getValue() instanceof Object[]) {
            Object[] values = (Object[]) annotation.getValue();
            addTermsFromAnnotationValue(values, false);
          } else if (annotation.getValue() instanceof AnnotatedTerm) {
            frame.setProof((AnnotatedTerm) annotation.getValue());
            processAnnotated(frame);
          } else if (annotation.getValue() instanceof ApplicationTerm) {
            formulas.add((Term) annotation.getValue());
          }
        }

        if (key.equals("rup")) {
          this.proofRule = Rup.RUP;
          //this.children.add(new ProvitionalProofNode(term.getSubterm()));
          frame.setNumArgs(1);
          if (!computed.containsKey(term.getSubterm())) {
            SmtTermFrame childFrame = new SmtTermFrame(term.getSubterm());
            stack.push(childFrame);
            frame.children.add(childFrame);
            //children.add(new ProvitionalProofNode(term.getSubterm()));
            computed.put(term.getSubterm(), new ProvitionalProofNode(term.getSubterm()));
          }
          rup = true;
        }

        if (key.equals("proves")) {
          Object[] values = (Object[]) annotation.getValue();
          addTermsFromAnnotationValue(values, true);
        }

      }
      if (!rup) {
        frame.setProof(term.getSubterm());
        processTerm(frame);
      }
    }

    void addTermsFromAnnotationValue(Object[] values, boolean isProves) {
      for (int i = 0; values.length > i; i++) {
        if (values[i] instanceof Term) {
          // We found a Term and the index before it should contain the polarity, but only if
          // this is the value of the proves Annotation.
          if (isProves) {
            assert values[i - 1].getClass() == String.class;
            if (((String) values[i - 1]).contains("+")) {
              this.formulas.add((Term) values[i]);
            } else {
              // We try to create the negative polarity Term
              this.formulas.add(Util.not(creator.getEnv(), (Term) values[i]));
            }
          } else {
            this.formulas.add((Term) values[i]);
          }

        }
      }
    }

    public String asString() {
      return asString(0);
    }

    String asString(int indentLevel) {
      StringBuilder sb = new StringBuilder();
      String indent = "  ".repeat(indentLevel);

      // Node header
      sb.append(indent).append("ProofNode {\n");

      // Node properties
      sb.append(indent).append("  pivot: ").append(pivot != null ? pivot : "null").append("\n");
      sb.append(indent).append("  proofRule: ")
          .append(proofRule != null ? proofRule.getName() : "null").append("\n");
      sb.append(indent).append("  axiom: ").append(axiom).append("\n");
      sb.append(indent).append("  isVisited: ").append(isVisited).append("\n");

      // Formulas
      sb.append(indent).append("  formulas: [\n");
      if (formulas.isEmpty()) {
        sb.append(indent).append("    empty\n");
      } else {
        for (Term formula : formulas) {
          sb.append(indent).append("    ").append(formula != null ? formula : "null").append("\n");
        }
      }
      sb.append(indent).append("  ]\n");

      // Unprocessed term
      sb.append(indent).append("  unprocessedTerm: ")
          .append(unprocessedTerm != null ? unprocessedTerm : "null")
          .append("\n");

      // Children nodes
      sb.append(indent).append("  children: [\n");
      if (children.isEmpty()) {
        sb.append(indent).append("    empty\n");
      } else {
        for (ProvitionalProofNode child : children) {
          if (child != null) {
            sb.append(child.asString(indentLevel + 2));
          } else {
            sb.append(indent).append("    null\n");
          }
        }
      }
      sb.append(indent).append("  ]\n");

      // Close node
      sb.append(indent).append("}\n");

      return sb.toString();
    }
  }
}
