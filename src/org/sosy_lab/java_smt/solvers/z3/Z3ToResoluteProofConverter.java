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

import static org.sosy_lab.java_smt.solvers.z3.Z3ProofRule.MODUS_PONENS;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import org.sosy_lab.java_smt.ResProofRule.ResAxiom;
import org.sosy_lab.java_smt.ResolutionProofDag;
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

import java.util.HashMap;
import java.util.Map;

/**
 * Converts a Z3 proof to a RESOLUTE proof.
 */

@SuppressWarnings({"unchecked", "rawtypes", "unused", "static-access"})
public class Z3ToResoluteProofConverter {

  private final Z3FormulaManager formulaManager;

  private final BooleanFormulaManager bfm;

   Z3ToResoluteProofConverter(Z3FormulaManager creator) {
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


   static ResolutionProofDag convertToResolutionProofDAG(Z3ProofNode[] z3ProofNodes) {
    ResolutionProofDag dag = new ResolutionProofDag();

    for (Z3ProofNode z3Node : z3ProofNodes) {
      if (z3Node.getRule() == MODUS_PONENS) {

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

  ProofNode handleNode(Z3ProofNode node) {
    Z3ProofRule rule = (Z3ProofRule) node.getRule();

    switch (rule) {
      case TRUE:
        return handleTrue(node);

      case ASSERTED:
        return handleAsserted(node);

      case GOAL:
        return handleAsserted(node);

      case MODUS_PONENS:
        return handleModusPonens(node);

      case REFLEXIVITY:
        return handleReflexivity(node);

      case SYMMETRY:
        return handleSymmetry(node);

      case TRANSITIVITY:
        return handleTransitivity(node);

      case TRANSITIVITY_STAR:
        return handleTransitivityStar(node);

      case MONOTONICITY:
        return handleMonotonicity(node);

      case QUANT_INTRO:
        return handleQuantIntro(node);

      case BIND:
        return handleBind(node);

      case DISTRIBUTIVITY:
        return handleDistributivity(node);

      case AND_ELIM:
        return handleAndElim(node);

      case NOT_OR_ELIM:
        return handleNotOrElim(node);

      case REWRITE:
        return handleRewrite(node);

      case REWRITE_STAR:
        return handleRewriteStar(node);

      case PULL_QUANT:
        return handlePullQuant(node);

      case PUSH_QUANT:
        return handlePushQuant(node);

      case ELIM_UNUSED_VARS:
        return handleElimUnusedVars(node);

      case DER:
        return handleDer(node);

      case QUANT_INST:
        return handleQuantInst(node);

      case HYPOTHESIS:
        return handleHypothesis(node);

      case LEMMA:
        return handleLemma(node);

      case UNIT_RESOLUTION:
        return handleUnitResolution(node);

      case IFF_TRUE:
        return handleIffTrue(node);

      case IFF_FALSE:
        return handleIffFalse(node);

      case COMMUTATIVITY:
        return handleCommutativity(node);

      case DEF_AXIOM:
        return handleDefAxiom(node);

      case ASSUMPTION_ADD:
        return handleAssumptionAdd(node);

      case LEMMA_ADD:
        return handleLemmaAdd(node);

      case REDUNDANT_DEL:
        return handleRedundantDel(node);

      case CLAUSE_TRAIL:
        return handleClauseTrail(node);

      case DEF_INTRO:
        return handleDefIntro(node);

      case APPLY_DEF:
        return handleApplyDef(node);

      case IFF_OEQ:
        return handleIffOeq(node);

      case NNF_POS:
        return handleNnfPos(node);

      case NNF_NEG:
        return handleNnfNeg(node);

      case SKOLEMIZE:
        return handleSkolemize(node);

      case MODUS_PONENS_OEQ:
        return handleModusPonensOeq(node);

      case TH_LEMMA:
        return handleThLemma(node);

      case HYPER_RESOLVE:
        return handleHyperResolve(node);

      case OPERATION:
        return handleOperation(node);

      default:
        return handleDefault(node);
    }
  }

  ProofNode handleTrue(Z3ProofNode node) {
    BooleanFormula formula = (BooleanFormula) node.getFormula();
    SourceProofNode pn = new SourceProofNode(ResAxiom.TRUE_POSITIVE, formula);
    return pn;
  }

  ProofNode handleAsserted(Z3ProofNode node) {
    BooleanFormula formula = (BooleanFormula) node.getFormula();
    SourceProofNode pn = new SourceProofNode(ResAxiom.ASSUME, formula);
    return pn;
  }

  ProofNode handleModusPonens(Z3ProofNode node) {
    BooleanFormula formula = (BooleanFormula) node.getFormula();
    BooleanFormula pivot = (BooleanFormula) node.getChildren().get(0).getFormula();
    ResolutionProofNode pn = new ResolutionProofNode(formula, pivot);
    ProofNode c1 = handleNode((Z3ProofNode) node.getChildren().get(0));
    ProofNode c2 = handleNode((Z3ProofNode) node.getChildren().get(1));
    return pn;
  }

  ProofNode handleReflexivity(Z3ProofNode node) {
    BooleanFormula formula = (BooleanFormula) node.getFormula();
    SourceProofNode pn = new SourceProofNode(ResAxiom.REFLEXIVITY, formula);
    return pn;
  }

  ProofNode handleSymmetry(Z3ProofNode node) {
    BooleanFormula formula = (BooleanFormula) node.getFormula();
    BooleanFormula pivot = (BooleanFormula) node.getChildren().get(0).getFormula();
    BooleanFormula snFormula = bfm.or(bfm.not(pivot), formula);

    ResolutionProofNode pn = new ResolutionProofNode(formula, pivot);
    SourceProofNode sn = new SourceProofNode(ResAxiom.SYMMETRY, snFormula);
    pn.addChild(sn);
    pn.addChild(handleNode((Z3ProofNode) node.getChildren().get(0)));
    return pn;
  }


  ProofNode handleTransitivity(Z3ProofNode node) {

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

  ProofNode handleTransitivityStar(Z3ProofNode node) {
    BooleanFormula resPivot = null;
     Collection<BooleanFormula> formulas = new ArrayList<>();
     List<Collection<BooleanFormula>> formulaList = new ArrayList<>();
     int numChildren = node.getChildren().size();

        for (int i = 0; i < numChildren; i++) {
          Collection<BooleanFormula> newCollection = new ArrayList<>();
          formulas.add(bfm.not((BooleanFormula) node.getChildren().get(i).getFormula()));
          if (i == numChildren - 1) {
            resPivot = (BooleanFormula) node.getChildren().get(i).getFormula();
          }
        }

    assert resPivot != null;
    ResolutionProofNode resNode = new ResolutionProofNode(node.getFormula(), resPivot);


        formulas.add((BooleanFormula) node.getFormula());
        BooleanFormula transitivityFormula = bfm.or(formulas);
        SourceProofNode sn = new SourceProofNode(ResAxiom.TRANSITIVITY, transitivityFormula);

        for (int i = 0; i < formulas.size()-2; i++){
          //ResolutionProofNode pn1 = new ResolutionProofNode(transitivityFormula.,
              //formulaList.get(i))
        }




    return resNode;
  }

  ProofNode handleMonotonicity(Z3ProofNode node) {
    return null;
  }

  ProofNode handleQuantIntro(Z3ProofNode node) {
    return null;
  }

  ProofNode handleBind(Z3ProofNode node) {
    return null;
  }

  ProofNode handleDistributivity(Z3ProofNode node) {
    return null;
  }

  ProofNode handleAndElim(Z3ProofNode node) {
    return null;
  }

  ProofNode handleNotOrElim(Z3ProofNode node) {
    return null;
  }

  ProofNode handleRewrite(Z3ProofNode node) {
    return null;
  }

  ProofNode handleRewriteStar(Z3ProofNode node) {
    return null;
  }

  ProofNode handlePullQuant(Z3ProofNode node) {
    return null;
  }

  ProofNode handleElimUnusedVars(Z3ProofNode node) {
    return null;
  }

  ProofNode handlePushQuant(Z3ProofNode node) {
    return null;
  }

  ProofNode handleDer(Z3ProofNode node) {
    return null;
  }

  ProofNode handleQuantInst(Z3ProofNode node) {
    return null;
  }

  ProofNode handleHypothesis(Z3ProofNode node) {
    return null;
  }

  ProofNode handleLemma(Z3ProofNode node) {
    return null;
  }

  ProofNode handleUnitResolution(Z3ProofNode node) {
    return null;
  }

  ProofNode handleIffTrue(Z3ProofNode node) {
    return null;
  }

  ProofNode handleIffFalse(Z3ProofNode node) {
    return null;
  }

  ProofNode handleCommutativity(Z3ProofNode node) {
    return null;
  }

  ProofNode handleDefAxiom(Z3ProofNode node) {
    return null;
  }

  ProofNode handleAssumptionAdd(Z3ProofNode node) {
    return null;
  }

  ProofNode handleLemmaAdd(Z3ProofNode node) {
    return null;
  }

  ProofNode handleRedundantDel(Z3ProofNode node) {
    return null;
  }

  ProofNode handleClauseTrail(Z3ProofNode node) {
    return null;
  }

  ProofNode handleDefIntro(Z3ProofNode node) {
    return null;
  }

  ProofNode handleApplyDef(Z3ProofNode node) {
    return null;
  }

  ProofNode handleIffOeq(Z3ProofNode node) {
    return null;
  }

  ProofNode handleNnfPos(Z3ProofNode node) {
    return null;
  }

  ProofNode handleNnfNeg(Z3ProofNode node) {
    return null;
  }

  ProofNode handleSkolemize(Z3ProofNode node) {
    return null;
  }

  ProofNode handleModusPonensOeq(Z3ProofNode node) {
    return null;
  }

  ProofNode handleThLemma(Z3ProofNode node) {
    return null;
  }

  ProofNode handleHyperResolve(Z3ProofNode node) {
    return null;
  }

  ProofNode handleOperation(Z3ProofNode node) {
    return null;
  }

  ProofNode handleDefault(Z3ProofNode node) {
    return null;
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
