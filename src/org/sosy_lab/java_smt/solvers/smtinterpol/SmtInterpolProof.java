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

import com.google.common.base.Preconditions;
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
import java.util.Locale;
import java.util.Map;
import org.sosy_lab.java_smt.ResProofRule;
import org.sosy_lab.java_smt.ResProofRule.ResAxiom;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.proofs.Proof;
import org.sosy_lab.java_smt.api.proofs.ProofRule;
import org.sosy_lab.java_smt.basicimpl.AbstractProof;
import org.sosy_lab.java_smt.solvers.smtinterpol.SmtInterpolProof.Rules;

/**
 * This class represents a SMTInterpol proof DAG in the JavaSMT proof interface. Many formulas that
 * are not in the leafs or are pivots for resolution are null, as SMTInterpol does not provide them.
 * Every resolution node has 3 chilren: sub-proof, pivot, sub-proof. There exists the RUP sub-proof,
 * these means that the stored formula was proven by applying RUP to the child of the node. The
 * PIVOT and RUP proof rules have been added to the proof format from SMTInterpol for the sake of
 * offering a proof rule at every step of the proof as well as allowing to display the pivots for
 * resolution steps.
 */
class SmtInterpolProof extends AbstractProof {
  protected enum Rules implements ProofRule {
    COEFFS("coeffs"),
    VALUES("values"),
    DIVISOR("divisor"),
    POS("pos"),
    UNIT("unit"),
    DEFINE_FUN("define-fun"),
    DECLARE_FUN("declare-fun"),
    RUP("rup"),
    PIVOT("pivot");
    final String name;

    Rules(String pDefineFun) {
      name = pDefineFun;
    }

    static Rules getFromName(String pName) {
      if (pName.equals("DEFINE-FUN")) {
        return DEFINE_FUN;
      } else if (pName.equals("DECLARE-FUN")) {
        return DECLARE_FUN;
      }
      return Rules.valueOf(pName);
    }

    @Override
    public String getName() {
      if (this.equals(DEFINE_FUN) || this.equals(DECLARE_FUN)) {
        return name;
      } else {
        return name().toLowerCase(Locale.ENGLISH);
      }
    }
  }

  SmtInterpolProof(ProofRule pRule, Formula pFormula) {
    super(pRule, pFormula);
  }

  @Override
  protected void addChild(Proof pProof) {
    super.addChild(pProof);
  }

  @Override
  public String proofAsString() {
    return super.proofAsString();
  }
}

class SmtInterpolProofNodeCreator {
  private final SmtInterpolFormulaCreator creator;

  SmtInterpolProofNodeCreator(SmtInterpolFormulaCreator pCreator) {
    creator = pCreator;
  }

  SmtInterpolProof createProof(ProvitionalProofNode pProofNode) {
    Deque<ProvitionalProofNode> stack = new ArrayDeque<>();
    Map<ProvitionalProofNode, SmtInterpolProof> computed = new HashMap<>();

    stack.push(pProofNode);

    while (!stack.isEmpty()) {
      ProvitionalProofNode proofNode = stack.peek();

      if (!proofNode.isVisited) {
        proofNode.isVisited = true;

        if (proofNode.proofRule.equals(ResAxiom.RESOLUTION)) {
          ProvitionalProofNode pivot = new ProvitionalProofNode();
          pivot.proofRule = Rules.PIVOT;
          pivot.formulas.add(proofNode.pivot);
          proofNode.children.add(1, pivot);
          for (ProvitionalProofNode child : proofNode.children) {
            stack.push(child);
          }
        } else {
          for (ProvitionalProofNode child : proofNode.children) {
            stack.push(child);
          }
        }
      } else {
        stack.pop();
        Formula formula = null;
        if (proofNode.formulas.size() > 1) {
          // This can not stay like this, the algorithm calculating the formulas to be stored is
          // needed, as what we retrieve here is simply arguments for generating a clause,
          // meaning the arguments do not have to be boolean and therefore joining them with OR
          // causes an exception.
          // Term or = Util.or(creator.getEnv(), proofNode.formulas.toArray(new Term[0]));
          // formula = creator.encapsulate(creator.getFormulaType(or), or);
        } else if (!proofNode.formulas.isEmpty()) {
          // We only know for sure what formulas are stored in the following cases. Otherwise, we
          // only have an input for generating the clauses after applying the RESOLUTE axioms.
          if (proofNode.proofRule.equals(ResAxiom.RESOLUTION)
              || proofNode.proofRule.equals(ResAxiom.ASSUME)
              || proofNode.proofRule.equals(Rules.RUP)
              || proofNode.proofRule.equals(Rules.PIVOT)) {
            Term t = proofNode.formulas.get(0);
            formula = creator.encapsulate(creator.getFormulaType(t), t);
          }
        }
        SmtInterpolProof pn = new SmtInterpolProof(proofNode.proofRule, formula);
        for (int i = 0; i < proofNode.children.size(); i++) {
          ProvitionalProofNode child = proofNode.children.get(i);
          if (computed.containsKey(child)) {
            pn.addChild(computed.get(child));
          }
        }
        computed.put(proofNode, pn);
      }
    }
    return computed.get(pProofNode);
  }

  ProvitionalProofNode createPPNDag(Term pTerm) {
    return new ProvitionalProofNode(pTerm);
  }

  class ProvitionalProofNode {
    Term pivot;
    ProofRule proofRule;
    List<Term> formulas = new ArrayList<>();
    boolean axiom;
    List<ProvitionalProofNode> children = new ArrayList<>();
    Term unprocessedTerm;
    boolean isVisited = false;

    ProvitionalProofNode() {}

    protected ProvitionalProofNode(Term pParameter) {
      this.unprocessedTerm = pParameter;
      processTerm(pParameter);
    }

    protected void processTerm(Term pParameter) {
      if (pParameter instanceof ApplicationTerm) {
        processApplication((ApplicationTerm) pParameter);
      } else if (pParameter instanceof AnnotatedTerm) {
        processAnnotated((AnnotatedTerm) pParameter);
      }
    }

    void processApplication(ApplicationTerm term) {
      Term[] parameters = term.getParameters();
      if (parameters.length == 3) {
        this.proofRule = ResAxiom.RESOLUTION;
        // This should be a resolution rule
        Term first = parameters[0];
        if (first instanceof AnnotatedTerm) {
          pivot = ((AnnotatedTerm) first).getSubterm();
        } else if (first instanceof ApplicationTerm) {
          pivot = first;
        }

        for (int i = 1; i < parameters.length; i++) {
          Sort sort = term.getSort();
          if (sort.toString().equals("..Proof")) {
            children.add(new ProvitionalProofNode(parameters[i]));
          }
        }
      }

      if (term.getFunction().toString().contains("..assume")) {
        // This should be the assume axiom
        this.axiom = true;
        this.proofRule = ResAxiom.ASSUME;
        if (parameters[0] instanceof AnnotatedTerm) {
          this.formulas.add(((AnnotatedTerm) parameters[0]).getSubterm());
        } else {
          this.formulas.add(parameters[0]);
        }
      }
    }

    private void processAnnotated(AnnotatedTerm term) {

      boolean rup = false;

      if (term.getSort().toString().equals("Bool")) {
        if (this.axiom) {
          this.pivot = term.getSubterm();
        } else {
          this.formulas.add(term.getSubterm());
        }
      }

      for (Annotation annotation : term.getAnnotations()) {
        ProofRule rule;
        String key = annotation.getKey().substring(1);

        if (term.getSubterm().toString().equals("..axiom")) {
          this.axiom = true;
          // Annotation key should contain axiom name and value should contain an array with some
          // of its objects being Terms and the index before each one of those contains the
          // polarity.
          key = key.startsWith(":") ? key.substring(1) : key;

          rule = ResProofRule.getFromName(key);
          if (rule == null) rule = Rules.getFromName(key.toUpperCase(Locale.ENGLISH));
          Preconditions.checkNotNull(key);

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
            processAnnotated((AnnotatedTerm) annotation.getValue());
          } else if (annotation.getValue() instanceof ApplicationTerm) {
            formulas.add((Term) annotation.getValue());
          }
        }

        if (key.equals("rup")) {
          this.proofRule = Rules.RUP;
          this.children.add(new ProvitionalProofNode(term.getSubterm()));
          rup = true;
        }

        if (key.equals("proves")) {
          Object[] values = (Object[]) annotation.getValue();
          addTermsFromAnnotationValue(values, true);
        }
      }
      if (!rup) {
        processTerm(term.getSubterm());
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

    // Just for testing purposes
    protected String proofAsString() {
      return proofAsString(0);
    }

    String proofAsString(int indentLevel) {
      StringBuilder sb = new StringBuilder();
      String indent = "  ".repeat(indentLevel);

      // Node header
      sb.append(indent).append("ProofNode {\n");

      // Node properties
      sb.append(indent).append("  pivot: ").append(pivot != null ? pivot : "null").append("\n");
      sb.append(indent)
          .append("  proofRule: ")
          .append(proofRule != null ? proofRule.getName() : "null")
          .append("\n");
      sb.append(indent).append("  axiom: ").append(axiom).append("\n");

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

      // Children nodes
      sb.append(indent).append("  children: [\n");
      if (children.isEmpty()) {
        sb.append(indent).append("    empty\n");
      } else {
        for (ProvitionalProofNode child : children) {
          if (child != null) {
            sb.append(child.proofAsString(indentLevel + 2));
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
