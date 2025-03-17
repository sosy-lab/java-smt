/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.z3;

import java.util.ArrayList;
import java.util.List;
import javax.xml.transform.Source;
import org.sosy_lab.java_smt.ResProofRule.ResAxiom;
import org.sosy_lab.java_smt.ResolutionProofDAG;
import org.sosy_lab.java_smt.ResolutionProofNode;
import org.sosy_lab.java_smt.SourceProofNode;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.proofs.ProofNode;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;
import org.sosy_lab.java_smt.solvers.z3.Z3ProofNode;
import org.sosy_lab.java_smt.solvers.z3.Z3ProofRule;

import java.util.HashMap;
import java.util.Map;


@SuppressWarnings({"unchecked", "rawtypes", "unused", "static-access"})
public class ProofConverter {

  private final Z3FormulaManager formulaManager;

  private final BooleanFormulaManager bfm;

  public ProofConverter(Z3FormulaManager creator) {
    formulaManager = creator;
    bfm = formulaManager.getBooleanFormulaManager();
  }

  private static final Map<Z3ProofRule, ResAxiom> ruleMapping = new HashMap<>();
/*
  static {
    ruleMapping.put(Z3ProofRule.UNDEF, ResAxiom.ORACLE);
    ruleMapping.put(Z3ProofRule.TRUE, ResAxiom.TRUE_POSITIVE);
    ruleMapping.put(Z3ProofRule.ASSERTED, ResAxiom.ASSUME);
    ruleMapping.put(Z3ProofRule.GOAL, ResAxiom.ASSUME);
    ruleMapping.put(Z3ProofRule.REFLEXIVITY, ResAxiom.REFLEXIVITY);
    ruleMapping.put(Z3ProofRule.SYMMETRY, ResAxiom.SYMMETRY);
    ruleMapping.put(Z3ProofRule.TRANSITIVITY, ResAxiom.TRANSITIVITY);
    ruleMapping.put(Z3ProofRule.TRANSITIVITY_STAR, ResAxiom.TRANSITIVITY_STAR);
    ruleMapping.put(Z3ProofRule.MONOTONICITY, ResAxiom.MONOTONICITY);
    ruleMapping.put(Z3ProofRule.QUANT_INTRO, ResAxiom.QUANT_INTRO);
    ruleMapping.put(Z3ProofRule.BIND, ResAxiom.BIND);
    ruleMapping.put(Z3ProofRule.DISTRIBUTIVITY, ResAxiom.DISTRIBUTIVITY);
    ruleMapping.put(Z3ProofRule.AND_ELIM, ResAxiom.AND_POSITIVE);
    ruleMapping.put(Z3ProofRule.NOT_OR_ELIM, ResAxiom.NOT_NEGATIVE);
    ruleMapping.put(Z3ProofRule.REWRITE, ResAxiom.REWRITE);
    ruleMapping.put(Z3ProofRule.REWRITE_STAR, ResAxiom.REWRITE_STAR);
    ruleMapping.put(Z3ProofRule.PULL_QUANT, ResAxiom.PULL_QUANT);
    ruleMapping.put(Z3ProofRule.PUSH_QUANT, ResAxiom.PUSH_QUANT);
    ruleMapping.put(Z3ProofRule.ELIM_UNUSED_VARS, ResAxiom.ELIM_UNUSED_VARS);
    ruleMapping.put(Z3ProofRule.DER, ResAxiom.DER);
    ruleMapping.put(Z3ProofRule.QUANT_INST, ResAxiom.QUANT_INST);
    ruleMapping.put(Z3ProofRule.HYPOTHESIS, ResAxiom.HYPOTHESIS);
    ruleMapping.put(Z3ProofRule.LEMMA, ResAxiom.LEMMA);
    ruleMapping.put(Z3ProofRule.UNIT_RESOLUTION, ResAxiom.UNIT_RESOLUTION);
    ruleMapping.put(Z3ProofRule.IFF_TRUE, ResAxiom.IFF_TRUE);
    ruleMapping.put(Z3ProofRule.IFF_FALSE, ResAxiom.IFF_FALSE);
    ruleMapping.put(Z3ProofRule.COMMUTATIVITY, ResAxiom.COMMUTATIVITY);
    ruleMapping.put(Z3ProofRule.DEF_AXIOM, ResAxiom.DEF_AXIOM);
    ruleMapping.put(Z3ProofRule.ASSUMPTION_ADD, ResAxiom.ASSUMPTION_ADD);
    ruleMapping.put(Z3ProofRule.LEMMA_ADD, ResAxiom.LEMMA_ADD);
    ruleMapping.put(Z3ProofRule.REDUNDANT_DEL, ResAxiom.REDUNDANT_DEL);
    ruleMapping.put(Z3ProofRule.CLAUSE_TRAIL, ResAxiom.CLAUSE_TRAIL);
    ruleMapping.put(Z3ProofRule.DEF_INTRO, ResAxiom.DEF_INTRO);
    ruleMapping.put(Z3ProofRule.APPLY_DEF, ResAxiom.APPLY_DEF);
    ruleMapping.put(Z3ProofRule.IFF_OEQ, ResAxiom.IFF_OEQ);
    ruleMapping.put(Z3ProofRule.NNF_POS, ResAxiom.NNF_POS);
    ruleMapping.put(Z3ProofRule.NNF_NEG, ResAxiom.NNF_NEG);
    ruleMapping.put(Z3ProofRule.SKOLEMIZE, ResAxiom.SKOLEMIZE);
    ruleMapping.put(Z3ProofRule.MODUS_PONENS_OEQ, ResAxiom.MODUS_PONENS_OEQ);
    ruleMapping.put(Z3ProofRule.TH_LEMMA, ResAxiom.TH_LEMMA);
    ruleMapping.put(Z3ProofRule.HYPER_RESOLVE, ResAxiom.HYPER_RESOLVE);
  }

 */

  /*
  public static ResAxiom mapRule(Z3ProofRule z3Rule) {
    return ruleMapping.getOrDefault(z3Rule, ResAxiom.OPERATION);
  }
   */


  public static ResolutionProofDAG convertToResolutionProofDAG(Z3ProofNode[] z3ProofNodes) {
    ResolutionProofDAG dag = new ResolutionProofDAG();

    for (Z3ProofNode z3Node : z3ProofNodes) {
      if (z3Node.getRule() == Z3ProofRule.MODUS_PONENS) {

      } else {
        Formula formula = z3Node.getFormula();
        //ResAxiom resAxiom = mapRule(z3Node.getRule());
        //SourceProofNode sourceNode = new SourceProofNode(resAxiom, formula);
        //dag.addNode(sourceNode);
      }
    }

    return dag;
  }

  private static class EquivalenceExtractor implements BooleanFormulaVisitor<TraversalProcess> {
    private final List<BooleanFormula> equivalenceOperands = new ArrayList<>();

    public List<BooleanFormula> getEquivalenceOperands() {
      return equivalenceOperands;
    }

    @Override
    public TraversalProcess visitEquivalence(BooleanFormula left, BooleanFormula right) {
      equivalenceOperands.add(left);
      equivalenceOperands.add(right);
      return TraversalProcess.CONTINUE;
    }

    @Override
    public TraversalProcess visitImplication(BooleanFormula operand1, BooleanFormula operand2) {
      return TraversalProcess.CONTINUE;
    }

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
      return TraversalProcess.CONTINUE;
    }

    @Override
    public TraversalProcess visitOr(List<BooleanFormula> operands) {
      return TraversalProcess.CONTINUE;
    }

    @Override
    public TraversalProcess visitXor(BooleanFormula operand1, BooleanFormula operand2) {
      return TraversalProcess.CONTINUE;
    }

    @Override
    public TraversalProcess visitIfThenElse(
        BooleanFormula condition,
        BooleanFormula thenFormula,
        BooleanFormula elseFormula) {
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
        BooleanFormula atom,
        FunctionDeclaration<BooleanFormula> funcDecl) {
      return TraversalProcess.CONTINUE;
    }
  }

  public List<BooleanFormula> extractEquivalenceOperands(BooleanFormula formula) {
    EquivalenceExtractor extractor = new EquivalenceExtractor();
    bfm.visitRecursively(formula, extractor);
    return extractor.getEquivalenceOperands();
  }

  ProofNode handleTrans(Z3ProofNode node) {

    BooleanFormula t1 = (BooleanFormula) node.getChildren().get(0).getFormula();
    BooleanFormula t2 = (BooleanFormula) node.getChildren().get(1).getFormula();
    BooleanFormula formula = (BooleanFormula) node.getFormula();

    List<BooleanFormula> equivalenceOperands1 = extractEquivalenceOperands(t1);
    List<BooleanFormula> equivalenceOperands2 = extractEquivalenceOperands(t2);

    assert equivalenceOperands1.get(1).equals(equivalenceOperands2.get(0));

    BooleanFormula transRes =
        formula;
    BooleanFormula transClause = bfm.or(bfm.not(t1),
        bfm.not(t2), formula);

    SourceProofNode pn = new SourceProofNode(ResAxiom.TRANSITIVITY, transClause);

    ResolutionProofNode transResNode = new ResolutionProofNode(transRes,
        t2);
    ResolutionProofNode trnAnte1 =
        new ResolutionProofNode(t2, t2);
    BooleanFormula trn2Formula = bfm.or(bfm.not(t2), transRes);
    ResolutionProofNode trnAnte2 = new ResolutionProofNode(trn2Formula, t1);
    ResolutionProofNode trnAnte2Ante = new ResolutionProofNode(t1, t1);

    transResNode.addChild(trnAnte1);
    transResNode.addChild(trnAnte2);
    trnAnte2.addChild(trnAnte2Ante);
    trnAnte2.addChild(pn);
    
    return transResNode;
  }

  void printProof(ProofNode node, int indentLevel) {
    String indent = "  ".repeat(indentLevel);

    if (node instanceof SourceProofNode) {
      SourceProofNode sourceNode = (SourceProofNode) node;
      System.out.println(indent + "Formula: " + sourceNode.getFormula());
      System.out.println(indent + "Rule: " + sourceNode.getRule());
      System.out.println(indent + "No. Children: " + sourceNode.getChildren().size());
      int i = 0;
      for (ProofNode child : sourceNode.getChildren()) {
        System.out.println(indent + "Child " + (++i) + ":");
        printProof(child, indentLevel + 1);
      }
    } else if (node instanceof ResolutionProofNode) {
      ResolutionProofNode resolutionNode = (ResolutionProofNode) node;
      System.out.println(indent + "Formula: " + resolutionNode.getFormula());
      System.out.println(indent + "Pivot: " + resolutionNode.getPivot());
      System.out.println(indent + "Rule: " + resolutionNode.getRule());
      System.out.println(indent + "No. Children: " + resolutionNode.getChildren().size());
      int i = 0;
      for (ProofNode child : resolutionNode.getChildren()) {
        System.out.println(indent + "Child " + (++i) + ":");
        printProof(child, indentLevel + 1);
      }
    } else {
      throw new AssertionError("Unknown proof node type");
    }
  }


}
