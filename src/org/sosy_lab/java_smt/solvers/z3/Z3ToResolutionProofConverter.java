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
import org.sosy_lab.java_smt.AxiomProof;
import org.sosy_lab.java_smt.ResProofRule.ResAxiom;
import org.sosy_lab.java_smt.ResolutionProof;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.proofs.Proof;
import org.sosy_lab.java_smt.api.visitors.BooleanFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

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

  Z3ToResolutionProofConverter(Z3FormulaManager creator) {
    formulaManager = creator;
    bfm = formulaManager.getBooleanFormulaManager();
  }

  private static final Map<Z3ProofRule, ResAxiom> ruleMapping = new HashMap<>();

  /**
   * This method converts a set of Z3ProofNodes into a {@link
   * org.sosy_lab.java_smt.ResolutionProof}.
   *
   * @param z3ProofNodes the nodes to be converted.
   * @return {@link org.sosy_lab.java_smt.ResolutionProof}
   */
  ResolutionProof convertToResolutionProofDag(Z3Proof[] z3ProofNodes) {

    for (Z3Proof z3Node : z3ProofNodes) {
      if (z3Node.getRule() == MODUS_PONENS) {
        continue; // process mp continue here to avoid empty if block
      } else {
        Formula formula = z3Node.getFormula();
        // ResAxiom resAxiom = mapRule(z3Node.getRule());
        // SourceProofNode sourceNode = new SourceProofNode(resAxiom, formula);
        // dag.addNode(sourceNode);
      }
    }
    throw new UnsupportedOperationException();
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
   * Converts a {@link Z3Proof} into either a {@link ResolutionProof} or a {@link AxiomProof},
   * depending on its rule.
   *
   * @param node the {@link Z3Proof} to convert
   * @return the resulting {@link Proof}
   */
  Proof handleNode(Z3Proof node) {
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
        handleDistributivity(node);

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

  Proof handleTrue(Z3Proof node) {
    BooleanFormula formula = (BooleanFormula) node.getFormula();
    AxiomProof pn = new AxiomProof(ResAxiom.TRUE_POSITIVE, formula);
    return pn;
  }

  Proof handleAsserted(Z3Proof node) {
    BooleanFormula formula = (BooleanFormula) node.getFormula();
    AxiomProof pn = new AxiomProof(ResAxiom.ASSUME, formula);
    return pn;
  }

  Proof handleModusPonens(Z3Proof node) {
    BooleanFormula formula = (BooleanFormula) node.getFormula();
    BooleanFormula pivot =
        (BooleanFormula) node.getChildren().stream().findFirst().get().getFormula();
    ResolutionProof pn = new ResolutionProof(formula, pivot);
    Proof c1 = handleNode((Z3Proof) node.getChildren().stream().findFirst().get());
    Proof c2 = handleNode((Z3Proof) new ArrayList<>(node.getChildren()).get(1));
    return pn;
  }

  Proof handleReflexivity(Z3Proof node) {
    BooleanFormula formula = (BooleanFormula) node.getFormula();
    AxiomProof pn = new AxiomProof(ResAxiom.REFLEXIVITY, formula);
    return pn;
  }

  Proof handleSymmetry(Z3Proof node) {
    BooleanFormula formula = (BooleanFormula) node.getFormula();
    BooleanFormula pivot =
        (BooleanFormula) node.getChildren().stream().findFirst().get().getFormula();
    BooleanFormula snFormula = bfm.or(bfm.not(pivot), formula);

    ResolutionProof pn = new ResolutionProof(formula, pivot);
    AxiomProof sn = new AxiomProof(ResAxiom.SYMMETRY, snFormula);
    pn.addChild(sn);
    pn.addChild(handleNode((Z3Proof) node.getChildren().stream().findFirst().get()));
    return pn;
  }

  Proof handleTransitivity(Z3Proof node) {

    BooleanFormula t1 = (BooleanFormula) node.getChildren().stream().findFirst().get().getFormula();
    BooleanFormula t2 = (BooleanFormula) new ArrayList<>(node.getChildren()).get(1).getFormula();
    BooleanFormula formula = (BooleanFormula) node.getFormula();

    List<BooleanFormula> equivalenceOperands1 = extractEquivalenceOperands(t1);
    List<BooleanFormula> equivalenceOperands2 = extractEquivalenceOperands(t2);

    assert equivalenceOperands1.get(1).equals(equivalenceOperands2.get(0));

    BooleanFormula transRes = formula;
    BooleanFormula transClause = bfm.or(bfm.not(t1), bfm.not(t2), formula);

    AxiomProof pn = new AxiomProof(ResAxiom.TRANSITIVITY, transClause);

    ResolutionProof transResNode = new ResolutionProof(transRes, t2);
    ResolutionProof trnAnte1 = new ResolutionProof(t2, t2);
    BooleanFormula trn2Formula = bfm.or(bfm.not(t2), transRes);
    ResolutionProof trnAnte2 = new ResolutionProof(trn2Formula, t1);
    ResolutionProof trnAnte2Ante = new ResolutionProof(t1, t1);

    transResNode.addChild(trnAnte1);
    transResNode.addChild(trnAnte2);
    trnAnte2.addChild(trnAnte2Ante);
    trnAnte2.addChild(pn);

    return transResNode;
  }

  // RESOLUTE has the transitivity axiom which we are using to create the transitivity leaf and
  // encode the transitivity star rule from Z3. The original proven formulas from the premises for
  // the Z3 proof are then used to perform resolution iteratively on the transitivity clause for the
  // resolution proof. The resulting node has the same formula as the initial node from Z3 but also
  // includes the pivot used in the last resolution step.
  Proof handleTransitivityStar(Z3Proof node) {
    return iterativeResolution(node, ResAxiom.TRANSITIVITY);
  }
  
  // There seems to be no equivalent singular axiom in RESOLUTE for the encoding of the
  // Z3_MONOTONICITY Proof Rule:
  // " Z3_OP_PR_MONOTONICITY: Monotonicity proof object.
  //
  //          T1: (R t_1 s_1)
  //          ...
  //          Tn: (R t_n s_n)
  //          [monotonicity T1 ... Tn]: (R (f t_1 ... t_n) (f s_1 ... s_n))
  //
  //     Remark: if t_i == s_i, then the antecedent Ti is suppressed.
  //     That is, reflexivity proofs are suppressed to save space."
  //     from: https://github.com/Z3Prover/z3/blob/master/src/api/z3_api.h
  // Possible strategy: use the oracle proof rule from RESOLUTE. Possibility: introduce the
  // oracle_(rule) proof rule, e.g.: oracle_Z3_monotonicity to be able to introduce the rule as a
  // clause: from ((R t_1 s_1) AND ... AND (R t_n s_n)) => (R (f t_1 ... t_n) (f s_1 ... s_n))
  // into (not (R t_1 s_1)) OR ... OR (not (R t_n s_n)) OR (R (f t_1 ... t_n) (f s_1 ... s_n))
 Proof handleMonotonicity(Z3Proof node) {
    return iterativeResolution(node, ResAxiom.ORACLE);
  }
  
  // From https://github.com/Z3Prover/z3/blob/master/src/api/z3_api.h:
  // Z3_OP_PR_MONOTONICITY: Monotonicity proof object.
  //
  //    T1: (R t_1 s_1)
  //    ...
  // Tn: (R t_n s_n)
  //    [monotonicity T1 ... Tn]: (R (f t_1 ... t_n) (f s_1 ... s_n))
  //
  // Remark: if t_i == s_i, then the antecedent Ti is suppressed.
  // That is, reflexivity proofs are suppressed to save space.
  Proof handleQuantIntro(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

// From https://github.com/Z3Prover/z3/blob/master/src/api/z3_api.h:
  // Z3_OP_PR_BIND: Given a proof p,
  // produces a proof of lambda x . p, where x are free variables in p.
  //
  //     T1: f
  //     [proof-bind T1] forall (x) f
  // Could not find a way to encode this with given axioms from RESOLUTE, so the default solution
  // is to use oracle to prove "NOT f OR (forall (x) f)" and use f as pivot from the proof of f to
  // resolve into "forall (x) f".
  Proof handleBind(Z3Proof node) {
    List<Proof> children = new ArrayList<>(node.getChildren());
    Proof child = children.get(0);
    BooleanFormula f = (BooleanFormula) child.getFormula();

    BooleanFormula forallF = (BooleanFormula) node.getFormula();

    BooleanFormula axiomFormula = bfm.or(bfm.not(f), forallF);
    AxiomProof axiom = new AxiomProof(ResAxiom.ORACLE, axiomFormula);

    ResolutionProof resNode = new ResolutionProof(forallF, f);
    resNode.addChild(axiom);
    resNode.addChild(child);

    return resNode;
  }

// From https://github.com/Z3Prover/z3/blob/master/src/api/z3_api.h:
  //  - Z3_OP_PR_DISTRIBUTIVITY: Distributivity proof object.
  //          Given that f (= or) distributes over g (= and), produces a proof for
  //          \nicebox{
  //          (= (f a (g c d))
  //             (g (f a c) (f a d)))
  //          }
  //          If f and g are associative, this proof also justifies the following equality:
  //          \nicebox{
  //          (= (f (g a b) (g c d))
  //             (g (f a c) (f a d) (f b c) (f b d)))
  //          }
  //          where each f and g can have arbitrary number of arguments.
  //
  //          This proof object has no antecedents.
  //          Remark. This rule is used by the CNF conversion pass and
  //          instantiated by f = or, and g = and.
  // For now skip this node and take the next step in the proof, RESOLUTE uses a combination of
  // axioms to do CNF conversion and does not need a proof of distributivity. If this proof rule
  // from Z3 is used for CNF conversion the next step could be useful for the resolution based
  // proof
  void handleDistributivity(Z3Proof node) {
    // do nothing
    // the parent node should be a proof step for CNF conversion that is more relevant to RESOLUTE
  }

  // Z3_OP_PR_AND_ELIM: Given a proof for (and l_1 ... l_n), produces a proof for l_i
  //
  //        T1: (and l_1 ... l_n)
  //        [and-elim T1]: l_i
  // This is exactly the RESOLUTE axiom "and-": (-(and l_1 ... l_n) +(l_i))
  // Introduce node with said axiom and use the proof T1 to resolve the conjunction and prove l_i
  // through resolution
  Proof handleAndElim(Z3Proof node) {

    List<Proof> children = new ArrayList<>(node.getChildren());
    Proof child = children.get(0);

    BooleanFormula t1 = (BooleanFormula) child.getFormula();
    BooleanFormula li = (BooleanFormula) node.getFormula();

    BooleanFormula axiomFormula = bfm.or(bfm.not(T1), li);
    AxiomProof axiom = new AxiomProof(ResAxiom.AND_NEGATIVE, axiomFormula);

    ResolutionProof res = new ResolutionProof(li, T1);
    res.addChild(axiom);
    res.addChild(child);

    return res;
  }

 // Z3_OP_PR_NOT_OR_ELIM: Given a proof for (not (or l_1 ... l_n)), produces a proof for (not l_i).
  //
  //         T1: (not (or l_1 ... l_n))
  //         [not-or-elim T1]: (not l_i)
  // This is exactly the RESOLUTE axiom "or+": (+(or l_1 ... l_n) -(l_i))
  // Introduce node with said axiom and use the proof T1 to resolve the conjunction and prove not
  // l_i through resolution  
  Proof handleNotOrElim(Z3Proof node) {

    List<Proof> children = new ArrayList<>(node.getChildren());
    Proof child = children.get(0);
    BooleanFormula t1 = (BooleanFormula) child.getFormula();

    BooleanFormula notLi = (BooleanFormula) node.getFormula();

    BooleanFormula orFormula = bfm.not(t1);

    BooleanFormula axiomFormula = bfm.or(orFormula, notLi);
    AxiomProof axiom = new AxiomProof(ResAxiom.OR_POSITIVE, axiomFormula);

    ResolutionProof resNode = new ResolutionProof(notLi, orFormula);
    resNode.addChild(axiom);
    resNode.addChild(child);

    return resNode;
  }


 // Z3_OP_PR_REWRITE: A proof for a local rewriting step (= t s).
  //        The head function symbol of t is interpreted.
  //
  //        This proof object has no antecedents.
  //        The conclusion of a rewrite rule is either an equality (= t s),
  //        an equivalence (iff t s), or equi-satisfiability (~ t s).
  //        Remark: if f is bool, then = is iff.
  //        Examples:
  //        \nicebox{
  //        (= (+ x 0) x)
  //        (= (+ x 1 2) (+ 3 x))
  //        (iff (or x false) x)
  //        }
  // the assume axiom should produce a proof that is semantically equivalent
  Proof handleRewrite(Z3Proof node) {

    BooleanFormula conclusion = (BooleanFormula) node.getFormula();

    AxiomProof axiom = new AxiomProof(ResAxiom.ASSUME, conclusion);

    return axiom;
  }

  // Z3_OP_PR_REWRITE_STAR: A proof for rewriting an expression t into an expression s.
  //       This proof object can have n antecedents.
  //       The antecedents are proofs for equalities used as substitution rules.
  //       The proof rule is used in a few cases. The cases are:
  //         - When applying contextual simplification (CONTEXT_SIMPLIFIER=true)
  //         - When converting bit-vectors to Booleans (BIT2BOOL=true)
  // Since this is also a rewrite, use the assume axiom here for the clause NOT (AND p0 ... pn)
  // OR (= t s) where pi is an antecedent. This lets us resolve all the antecedents with this
  // clause and conclude (= t s)
   Proof handleRewriteStar(Z3Proof node) {
    return iterativeResolution(node, ResAxiom.ASSUME);
  }

  Proof handlePullQuant(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleElimUnusedVars(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handlePushQuant(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleDer(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleQuantInst(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleHypothesis(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleLemma(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleUnitResolution(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleIffTrue(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleIffFalse(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleCommutativity(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleDefAxiom(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleAssumptionAdd(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleLemmaAdd(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleRedundantDel(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleClauseTrail(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleDefIntro(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleApplyDef(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleIffOeq(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleNnfPos(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleNnfNeg(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleSkolemize(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleModusPonensOeq(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleThLemma(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleHyperResolve(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleOperation(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  Proof handleDefault(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

 //Creates a subtree of resolution rule applications
  private ResolutionProof iterativeResolution(Z3Proof node, ResAxiom axiom) {
    List<Proof> children = new ArrayList<>(node.getChildren());
    int n = children.size();
    List<BooleanFormula> formulas = new ArrayList<>();

    for (int i = 0; i < n; i++) {
      formulas.add(bfm.not((BooleanFormula) children.get(i).getFormula()));
    }

    formulas.add((BooleanFormula) node.getFormula());

    BooleanFormula axiomFormula = bfm.or(formulas);
    AxiomProof ax = new AxiomProof(axiom, axiomFormula);

    Formula resPivot = children.get(n - 1).getFormula();
    ResolutionProof resNode = new ResolutionProof(node.getFormula(), resPivot);

    Proof childNode = ax;
    for (int i = 0; i < n - 1; i++) {
      resPivot = children.get(i).getFormula();
      assert formulas.get(0).equals(bfm.not((BooleanFormula) resPivot));
      formulas.remove(0);
      ResolutionProof rp = new ResolutionProof(bfm.or(formulas), resPivot);
      rp.addChild(childNode);
      rp.addChild(children.get(i));
      childNode = rp;
    }

    resNode.addChild(childNode);
    resNode.addChild(children.get(n - 1));

    return resNode;
  }
  
  // This is for debugging purposes.
  void printProof(Proof node, int indentLevel) {
    String indent = "  ".repeat(indentLevel);

    if (node instanceof AxiomProof) {
      AxiomProof sourceNode = (AxiomProof) node;
      System.out.println(indent + "Formula: " + sourceNode.getFormula());
      System.out.println(indent + "Rule: " + sourceNode.getRule());
      System.out.println(indent + "No. Children: " + sourceNode.getChildren().size());
      int i = 0;
      for (Proof child : sourceNode.getChildren()) {
        System.out.println(indent + "Child " + ++i + ":");
        printProof(child, indentLevel + 1);
      }
    } else if (node instanceof ResolutionProof) {
      ResolutionProof resolutionNode = (ResolutionProof) node;
      System.out.println(indent + "Formula: " + resolutionNode.getFormula());
      System.out.println(indent + "Pivot: " + resolutionNode.getPivot());
      System.out.println(indent + "Rule: " + resolutionNode.getRule());
      System.out.println(indent + "No. Children: " + resolutionNode.getChildren().size());
      int i = 0;
      for (Proof child : resolutionNode.getChildren()) {
        System.out.println(indent + "Child " + ++i + ":");
        printProof(child, indentLevel + 1);
      }
    } else {
      throw new AssertionError("Unknown proof node type");
    }
  }
}
