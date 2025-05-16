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
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.sosy_lab.java_smt.ResProofRule.ResAxiom;
import org.sosy_lab.java_smt.ResolutionProof;
import org.sosy_lab.java_smt.ResolutionProof.AxiomSubproof;
import org.sosy_lab.java_smt.ResolutionProof.ResolutionSubproof;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.proofs.Proof.Subproof;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;
import org.sosy_lab.java_smt.solvers.z3.Z3Proof.Z3Subproof;

/**
 * Converts a Z3 proof into a format based on the RESOLUTE proof format.
 *
 * <p>The RESOLUTE format is a low-level proof format used by SMTInterpol. It exclusively relies on
 * the resolution rule, with multiple axioms defined to support various theories. These axioms serve
 * as the leaf nodes in the proof DAG. The strategy used is to transform each result from a Z3 proof
 * into corresponding resolution proof nodes, aiming to maintain the formulas used as arguments for
 * the Z3 proof rule as well as the result. Depending on the rule, the number of nodes may remain
 * the same (e.g., for modus ponens) or increase (e.g., for transitivity star). For the transitivity
 * star rule, the sub-proof grows approximately <code>2n-1</code> times, where <code>n</code> is the
 * number of nodes in the sub-proof.
 *
 * @see Z3ProofRule for the list of Z3 proof rules.
 * @see org.sosy_lab.java_smt.ResProofRule for the list of RESOLUTE axioms.
 */
@SuppressWarnings({"unchecked", "rawtypes", "unused", "static-access", "ModifiedButNotUsed"})
public class Z3ToResolutionProofConverter { // This class is inclompete and currently not used. The
  // strategy for transforming proof rules should be proved first.
  private final Z3FormulaManager formulaManager;

  private final BooleanFormulaManager bfm;

  private Z3Proof proof;

  Z3ToResolutionProofConverter(Z3FormulaManager creator) {
    formulaManager = creator;
    bfm = formulaManager.getBooleanFormulaManager();
    proof = new Z3Proof();
  }

  private static final Map<Z3ProofRule, ResAxiom> ruleMapping = new HashMap<>();

  /**
   * This method converts a set of Z3ProofNodes into a {@link ResolutionProof}.
   *
   * @param z3ProofNodes the nodes to be converted.
   * @return {@link ResolutionProof}
   */
  ResolutionProof convertToResolutionProofDag(Z3Subproof[] z3ProofNodes) {
    ResolutionProof dag = new ResolutionProof();
    this.proof = (Z3Proof) z3ProofNodes[0].getDAG();

    for (Z3Subproof z3Node : z3ProofNodes) {
      if (z3Node.getRule() == MODUS_PONENS) {
        continue; // process mp continue here to avoid empty if block
      } else {
        Formula formula = z3Node.getFormula();
        // ResAxiom resAxiom = mapRule(z3Node.getRule());
        // SourceProofNode sourceNode = new SourceProofNode(resAxiom, formula);
        // dag.addNode(sourceNode);
      }
    }

    return dag;
  }

  // This should help extract parts of a formula to better transform proof rules.
  private static final class ExtractorVisitor implements BooleanFormulaVisitor<TraversalProcess> {
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
        BooleanFormula condition, BooleanFormula thenFormula, BooleanFormula elseFormula) {
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
        BooleanFormula atom, FunctionDeclaration<BooleanFormula> funcDecl) {
      return TraversalProcess.CONTINUE;
    }
  }

  public List<BooleanFormula> extractEquivalenceOperands(BooleanFormula formula) {
    ExtractorVisitor extractor = new ExtractorVisitor();
    bfm.visitRecursively(formula, extractor);
    return extractor.getEquivalenceOperands();
  }

  /**
   * Converts a {@link Z3Subproof} into either a {@link ResolutionSubproof} or a {@link
   * AxiomSubproof}, depending on its rule.
   *
   * @param node the {@link Z3Subproof} to convert
   * @return the resulting {@link Subproof}
   */
  Subproof handleNode(Z3Subproof node) {
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

  Subproof handleTrue(Z3Subproof node) {
    BooleanFormula formula = (BooleanFormula) node.getFormula();
    AxiomSubproof pn = new AxiomSubproof(ResAxiom.TRUE_POSITIVE, formula, proof);
    return pn;
  }

  Subproof handleAsserted(Z3Subproof node) {
    BooleanFormula formula = (BooleanFormula) node.getFormula();
    AxiomSubproof pn = new AxiomSubproof(ResAxiom.ASSUME, formula, proof);
    return pn;
  }

  Subproof handleModusPonens(Z3Subproof node) {
    BooleanFormula formula = (BooleanFormula) node.getFormula();
    BooleanFormula pivot =
        (BooleanFormula) node.getArguments().stream().findFirst().get().getFormula();
    ResolutionSubproof pn = new ResolutionSubproof(formula, pivot, proof);
    Subproof c1 = handleNode((Z3Subproof) node.getArguments().stream().findFirst().get());
    Subproof c2 = handleNode((Z3Subproof) new ArrayList<>(node.getArguments()).get(1));
    return pn;
  }

  Subproof handleReflexivity(Z3Subproof node) {
    BooleanFormula formula = (BooleanFormula) node.getFormula();
    AxiomSubproof pn = new AxiomSubproof(ResAxiom.REFLEXIVITY, formula, proof);
    return pn;
  }

  Subproof handleSymmetry(Z3Subproof node) {
    BooleanFormula formula = (BooleanFormula) node.getFormula();
    BooleanFormula pivot = (BooleanFormula) node.getArguments().stream().findFirst().get().getFormula();
    BooleanFormula snFormula = bfm.or(bfm.not(pivot), formula);

    ResolutionSubproof pn = new ResolutionSubproof(formula, pivot, proof);
    AxiomSubproof sn = new AxiomSubproof(ResAxiom.SYMMETRY, snFormula, proof);
    pn.addChild(sn);
    pn.addChild(handleNode((Z3Subproof) node.getArguments().stream().findFirst().get()));
    return pn;
  }

  Subproof handleTransitivity(Z3Subproof node) {

    BooleanFormula t1 = (BooleanFormula) node.getArguments().stream().findFirst().get().getFormula();
    BooleanFormula t2 = (BooleanFormula) new ArrayList<>(node.getArguments()).get(1).getFormula();
    BooleanFormula formula = (BooleanFormula) node.getFormula();

    List<BooleanFormula> equivalenceOperands1 = extractEquivalenceOperands(t1);
    List<BooleanFormula> equivalenceOperands2 = extractEquivalenceOperands(t2);

    assert equivalenceOperands1.get(1).equals(equivalenceOperands2.get(0));

    BooleanFormula transRes = formula;
    BooleanFormula transClause = bfm.or(bfm.not(t1), bfm.not(t2), formula);

    AxiomSubproof pn = new AxiomSubproof(ResAxiom.TRANSITIVITY, transClause, proof);

    ResolutionSubproof transResNode = new ResolutionSubproof(transRes, t2, proof);
    ResolutionSubproof trnAnte1 = new ResolutionSubproof(t2, t2, proof);
    BooleanFormula trn2Formula = bfm.or(bfm.not(t2), transRes);
    ResolutionSubproof trnAnte2 = new ResolutionSubproof(trn2Formula, t1, proof);
    ResolutionSubproof trnAnte2Ante = new ResolutionSubproof(t1, t1, proof);

    transResNode.addChild(trnAnte1);
    transResNode.addChild(trnAnte2);
    trnAnte2.addChild(trnAnte2Ante);
    trnAnte2.addChild(pn);

    return transResNode;
  }

  Subproof handleTransitivityStar(Z3Subproof node) {
    BooleanFormula resPivot = null;
    Collection<BooleanFormula> formulas = new ArrayList<>();
    List<Collection<BooleanFormula>> formulaList = new ArrayList<>();
    int numChildren = node.getArguments().size();

    for (int i = 0; i < numChildren; i++) {
      Collection<BooleanFormula> newCollection = new ArrayList<>();
      formulas.add(bfm.not((BooleanFormula) new ArrayList<>(node.getArguments()).get(i).getFormula()));
      if (i == numChildren - 1) {
        resPivot = (BooleanFormula) new ArrayList<>(node.getArguments()).get(i).getFormula();
      }
    }

    assert resPivot != null;
    ResolutionSubproof resNode = new ResolutionSubproof(node.getFormula(), resPivot, proof);

    formulas.add((BooleanFormula) node.getFormula());
    BooleanFormula transitivityFormula = bfm.or(formulas);
    AxiomSubproof sn = new AxiomSubproof(ResAxiom.TRANSITIVITY, transitivityFormula, proof);

    for (int i = 0; i < formulas.size() - 2; i++) {
      // ResolutionProofNode pn1 = new ResolutionProofNode(transitivityFormula.,
      // formulaList.get(i))
    }

    return resNode;
  }

  Subproof handleMonotonicity(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleQuantIntro(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleBind(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleDistributivity(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleAndElim(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleNotOrElim(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleRewrite(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleRewriteStar(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handlePullQuant(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleElimUnusedVars(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handlePushQuant(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleDer(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleQuantInst(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleHypothesis(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleLemma(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleUnitResolution(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleIffTrue(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleIffFalse(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleCommutativity(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleDefAxiom(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleAssumptionAdd(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleLemmaAdd(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleRedundantDel(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleClauseTrail(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleDefIntro(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleApplyDef(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleIffOeq(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleNnfPos(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleNnfNeg(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleSkolemize(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleModusPonensOeq(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleThLemma(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleHyperResolve(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleOperation(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  Subproof handleDefault(Z3Subproof node) {
    throw new UnsupportedOperationException();
  }

  // This is for debugging purposes.
  void printProof(Subproof node, int indentLevel) {
    String indent = "  ".repeat(indentLevel);

    if (node instanceof AxiomSubproof) {
      AxiomSubproof sourceNode = (AxiomSubproof) node;
      System.out.println(indent + "Formula: " + sourceNode.getFormula());
      System.out.println(indent + "Rule: " + sourceNode.getRule());
      System.out.println(indent + "No. Children: " + sourceNode.getArguments().size());
      int i = 0;
      for (Subproof child : sourceNode.getArguments()) {
        System.out.println(indent + "Child " + ++i + ":");
        printProof(child, indentLevel + 1);
      }
    } else if (node instanceof ResolutionSubproof) {
      ResolutionSubproof resolutionNode = (ResolutionSubproof) node;
      System.out.println(indent + "Formula: " + resolutionNode.getFormula());
      System.out.println(indent + "Pivot: " + resolutionNode.getPivot());
      System.out.println(indent + "Rule: " + resolutionNode.getRule());
      System.out.println(indent + "No. Children: " + resolutionNode.getArguments().size());
      int i = 0;
      for (Subproof child : resolutionNode.getArguments()) {
        System.out.println(indent + "Child " + ++i + ":");
        printProof(child, indentLevel + 1);
      }
    } else {
      throw new AssertionError("Unknown proof node type");
    }
  }
}
