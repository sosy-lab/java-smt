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
  ResolutionProof convertToResolutionProofDag(Z3Proof z3ProofNodes) {

    throw new UnsupportedOperationException();
  }

  // This should help extract parts of a formula to better transform proof rules.
  private static final class ExtractorVisitor implements BooleanFormulaVisitor<TraversalProcess> {
    private final List<BooleanFormula> operands = new ArrayList<>();

    public List<BooleanFormula> getOperands() {
      return operands;
    }

    @Override
    public TraversalProcess visitEquivalence(BooleanFormula left, BooleanFormula right) {
      operands.add(left);
      operands.add(right);
      return TraversalProcess.ABORT;
    }

    @Override
    public TraversalProcess visitImplication(BooleanFormula operand1, BooleanFormula operand2) {
      return TraversalProcess.ABORT;
    }

    @Override
    public TraversalProcess visitConstant(boolean value) {
      return TraversalProcess.ABORT;
    }

    @Override
    public TraversalProcess visitBoundVar(BooleanFormula var, int deBruijnIdx) {
      return TraversalProcess.ABORT;
    }

    @Override
    public TraversalProcess visitNot(BooleanFormula operand) {
      operands.add(operand);
      return TraversalProcess.ABORT;
    }

    @Override
    public TraversalProcess visitAnd(List<BooleanFormula> operands) {
      return TraversalProcess.ABORT;
    }

    @Override
    public TraversalProcess visitOr(List<BooleanFormula> operands) {
      this.operands.addAll(operands);
      return TraversalProcess.ABORT;
    }

    @Override
    public TraversalProcess visitXor(BooleanFormula operand1, BooleanFormula operand2) {
      return TraversalProcess.ABORT;
    }

    @Override
    public TraversalProcess visitIfThenElse(
        BooleanFormula condition, BooleanFormula thenFormula, BooleanFormula elseFormula) {
      return TraversalProcess.ABORT;
    }

    @Override
    public TraversalProcess visitQuantifier(
        Quantifier quantifier,
        BooleanFormula quantifiedAST,
        List<Formula> boundVars,
        BooleanFormula body) {
      return TraversalProcess.ABORT;
    }

    @Override
    public TraversalProcess visitAtom(
        BooleanFormula atom, FunctionDeclaration<BooleanFormula> funcDecl) {
      return TraversalProcess.ABORT;
    }
  }

  public List<BooleanFormula> extractOperands(BooleanFormula formula) {
    ExtractorVisitor extractor = new ExtractorVisitor();
    bfm.visitRecursively(formula, extractor);
    return extractor.getOperands();
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
        handleIffTrue(node);

      case IFF_FALSE:
        handleIffFalse(node);

      case COMMUTATIVITY:
        handleCommutativity(node);

      case DEF_AXIOM:
        return handleDefAxiom(node);

      case ASSUMPTION_ADD:
        return handleAssumptionAdd(node);

      case LEMMA_ADD:
        return handleLemmaAdd(node);

      case REDUNDANT_DEL:
        return handleRedundantDel(node);

      case CLAUSE_TRAIL:
        handleClauseTrail(node);

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

    List<BooleanFormula> equivalenceOperands1 = extractOperands(t1);
    List<BooleanFormula> equivalenceOperands2 = extractOperands(t2);

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
    return iterativeResolutionWithAxiom(node, ResAxiom.TRANSITIVITY);
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
    return iterativeResolutionWithAxiom(node, ResAxiom.ORACLE);
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

    BooleanFormula axiomFormula = bfm.or(bfm.not(t1), li);
    AxiomProof axiom = new AxiomProof(ResAxiom.AND_NEGATIVE, axiomFormula);

    ResolutionProof resNode = new ResolutionProof(li, t1);
    resNode.addChild(axiom);
    resNode.addChild(child);

    return resNode;
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
    return iterativeResolutionWithAxiom(node, ResAxiom.ASSUME);
  }

  // Z3_OP_PR_PULL_QUANT: A proof for (iff (f (forall (x) q(x)) r) (forall (x) (f (q x) r))).
  // This proof object has no antecedents.
  Proof handlePullQuant(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  // Z3_OP_PR_ELIM_UNUSED_VARS:
  //          A proof for (iff (forall (x_1 ... x_n y_1 ... y_m) p[x_1 ... x_n])
  //                           (forall (x_1 ... x_n) p[x_1 ... x_n]))
  //
  //          It is used to justify the elimination of unused variables.
  //          This proof object has no antecedents.
  // Assume the equivalency. If this is used to substitute all occurrences of (forall (x_1 ...
  // x_n y_1 ... y_m) p[x_1 ... x_n]) with (forall (x_1 ... x_n) p[x_1 ... x_n]) then a more
  // complex process is needed.
  Proof handleElimUnusedVars(Z3Proof node) {
    BooleanFormula conclusion = (BooleanFormula) node.getFormula();
    AxiomProof axiom = new AxiomProof(ResAxiom.ASSUME, conclusion);
    return axiom;
  }

  // Z3_OP_PR_PUSH_QUANT: A proof for:
  //       \nicebox{
  //          (iff (forall (x_1 ... x_m) (and p_1[x_1 ... x_m] ... p_n[x_1 ... x_m]))
  //               (and (forall (x_1 ... x_m) p_1[x_1 ... x_m])
  //                 ...
  //               (forall (x_1 ... x_m) p_n[x_1 ... x_m])))
  //               }
  //         This proof object has no antecedents.
  Proof handlePushQuant(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  // Z3_OP_PR_DER: A proof for destructive equality resolution:
  //          (iff (forall (x) (or (not (= x t)) P[x])) P[t])
  //          if x does not occur in t.
  //
  //          This proof object has no antecedents.
  //
  //          Several variables can be eliminated simultaneously.
  // Analogous to the UNUSED_VARS rule.
  Proof handleDer(Z3Proof node) {
    BooleanFormula conclusion = (BooleanFormula) node.getFormula();
    AxiomProof axiom = new AxiomProof(ResAxiom.ASSUME, conclusion);
    return axiom;
  }

  // Z3_OP_PR_QUANT_INST: A proof of (or (not (forall (x) (P x))) (P a))
  // This is equivalent to the forall- axiom
  Proof handleQuantInst(Z3Proof node) {
    BooleanFormula formula = (BooleanFormula) node.getFormula();
    AxiomProof axiomProof = new AxiomProof(ResAxiom.FORALL_NEGATIVE, formula);
    return axiomProof;
  }

  // Z3_OP_PR_HYPOTHESIS: Mark a hypothesis in a natural deduction style proof.
  // Assume the hypothesis
  Proof handleHypothesis(Z3Proof node) {
    BooleanFormula conclusion = (BooleanFormula) node.getFormula();
    AxiomProof axiom = new AxiomProof(ResAxiom.ASSUME, conclusion);
    return axiom;
  }

  // Z3_OP_PR_LEMMA:
  //
  //          T1: false
  //          [lemma T1]: (or (not l_1) ... (not l_n))
  //
  //      This proof object has one antecedent: a hypothetical proof for false.
  //      It converts the proof in a proof for (or (not l_1) ... (not l_n)),
  //      when T1 contains the open hypotheses: l_1, ..., l_n.
  //      The hypotheses are closed after an application of a lemma.
  //      Furthermore, there are no other open hypotheses in the subtree covered by
  //      the lemma.
  Proof handleLemma(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  // Z3_OP_PR_UNIT_RESOLUTION:
  //       \nicebox{
  //          T1:      (or l_1 ... l_n l_1' ... l_m')
  //          T2:      (not l_1)
  //          ...
  //          T(n+1):  (not l_n)
  //          [unit-resolution T1 ... T(n+1)]: (or l_1' ... l_m')
  //          }
  // Resolve one by one, creating a resolution step for every Ti in the proof.
  Proof handleUnitResolution(Z3Proof node) {
    List<Proof> children = new ArrayList<>(node.getChildren());
    int n = children.size();

    // First child is the large disjunction
    Proof currentRes = children.get(0);

    // Resolve iteratively with each subsequent "not l_i"
    for (int i = 1; i < n; i++) {
      Proof negChild = children.get(i);
      BooleanFormula pivot = extractOperands((BooleanFormula) negChild.getFormula()).get(0);
      List<BooleanFormula> operands = extractOperands((BooleanFormula) currentRes.getFormula());
      operands.remove(0);
      BooleanFormula formula = bfm.or(operands);
      ResolutionProof resNode = new ResolutionProof(formula, pivot);
      resNode.addChild(currentRes);
      resNode.addChild(negChild);
      currentRes = resNode;
    }

    return currentRes;
  }

  // Z3_OP_PR_IFF_TRUE:
  //      \nicebox{
  //       T1: p
  //       [iff-true T1]: (iff p true)
  //       }
  // it proves the equivalence of p. Leaving as is will be tested otherwise using the
  // BooleanFormulaManager.makeTrue() method should work.
  void handleIffTrue(Z3Proof node) {
    // do nothing
  }

  // Z3_OP_PR_IFF_FALSE:
  //      \nicebox{
  //       T1: (not p)
  //       [iff-false T1]: (iff p false)
  //       }
  // it proves the equivalence of p. Leaving as is will be tested otherwise using the
  // BooleanFormulaManager.makeFalse() method should work.
  void handleIffFalse(Z3Proof node) {
    // do nothing
  }

  // Z3_OP_PR_COMMUTATIVITY:
  //
  //          [comm]: (= (f a b) (f b a))
  //
  //          f is a commutative operator.
  //
  //          This proof object has no antecedents.
  //          Remark: if f is bool, then = is iff.
  // similar case to handleDistributivity
  void handleCommutativity(Z3Proof node) {
    // do nothing
  }

  // Z3_OP_PR_DEF_AXIOM: Proof object used to justify Tseitin's like axioms:
  //          \nicebox{
  //          (or (not (and p q)) p)
  //          (or (not (and p q)) q)
  //          (or (not (and p q r)) p)
  //          (or (not (and p q r)) q)
  //          (or (not (and p q r)) r)
  //          ...
  //          (or (and p q) (not p) (not q))
  //          (or (not (or p q)) p q)
  //          (or (or p q) (not p))
  //          (or (or p q) (not q))
  //          (or (not (iff p q)) (not p) q)
  //          (or (not (iff p q)) p (not q))
  //          (or (iff p q) (not p) (not q))
  //          (or (iff p q) p q)
  //          (or (not (ite a b c)) (not a) b)
  //          (or (not (ite a b c)) a c)
  //          (or (ite a b c) (not a) (not b))
  //          (or (ite a b c) a (not c))
  //          (or (not (not a)) (not a))
  //          (or (not a) a)
  //          }
  //          This proof object has no antecedents.
  //          Note: all axioms are propositional tautologies.
  //          Note also that 'and' and 'or' can take multiple arguments.
  //          You can recover the propositional tautologies by
  //          unfolding the Boolean connectives in the axioms a small
  //          bounded number of steps (=3).
  // Assume formula proven by this rule.
  Proof handleDefAxiom(Z3Proof node) {
    BooleanFormula conclusion = (BooleanFormula) node.getFormula();
    AxiomProof axiom = new AxiomProof(ResAxiom.ASSUME, conclusion);
    return axiom;
  }

  // Z3_OP_PR_ASSUMPTION_ADD
  //     Clausal proof adding axiom
  // assume formula
  Proof handleAssumptionAdd(Z3Proof node) {
    BooleanFormula conclusion = (BooleanFormula) node.getFormula();
    AxiomProof axiom = new AxiomProof(ResAxiom.ASSUME, conclusion);
    return axiom;
  }

  // Z3_OP_PR_LEMMA_ADD
  //     Clausal proof lemma addition
  // assume formula
  Proof handleLemmaAdd(Z3Proof node) {
    BooleanFormula conclusion = (BooleanFormula) node.getFormula();
    AxiomProof axiom = new AxiomProof(ResAxiom.ASSUME, conclusion);
    return axiom;
  }

  // Z3_OP_PR_REDUNDANT_DEL
  //     Clausal proof lemma deletion
  // Possibility: delete whole subtree that was derived from using the redundant lemma. otherwise
  // resolve it from clauses that may contain it.
  Proof handleRedundantDel(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  // Z3_OP_PR_CLAUSE_TRAIL,
  //     Clausal proof trail of additions and deletions
  // this tracks the applications of additions and deletions.
  void handleClauseTrail(Z3Proof node) {
    // do nothing
  }

  // Z3_OP_PR_DEF_INTRO: Introduces a name for a formula/term.
  //     Suppose e is an expression with free variables x, and def-intro
  //     introduces the name n(x). The possible cases are:
  //
  //     When e is of Boolean type:
  //     [def-intro]: (and (or n (not e)) (or (not n) e))
  //
  //     or:
  //     [def-intro]: (or (not n) e)
  //     when e only occurs positively.
  //
  //     When e is of the form (ite cond th el):
  //     [def-intro]: (and (or (not cond) (= n th)) (or cond (= n el)))
  //
  //     Otherwise:
  //     [def-intro]: (= n e)
  //
  // Check form of the formula proven.
  //
  //  When e is of Boolean type - ((not e ) or n) and ((not n) or e)) -:
  //    ...
  //
  //  When e only occurs positively - (or (not n) e) -:
  //    we use the axiom 'or+' which produces '(+ (or (not n) e) - e)' assuming e (the
  //    expression) we can resolve e and get the original.
  //
  //  ...
  //
  // The way it is done in the second case could be expanded to the other cases. Otherwise, it is a
  // possibility to implement the oracle rule with different inputs.
  // It should be possible to introduce names with the 'let' operator, as well as the way it is
  // done by Z3. So another option is to use said operator here.
  Proof handleDefIntro(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  // Z3_OP_PR_APPLY_DEF:
  //
  //        [apply-def T1]: F ~ n
  //
  //     F is 'equivalent' to n, given that T1 is a proof that
  //     n is a name for F.
  //
  // This rule depends on the implementation of the DEF_INTRO rule. if using 'let' this step
  // might not be needed, otherwise should be kept. According to the paper found here:
  // https://www21.in.tum.de/~boehmes/proof-reconstruction.html
  // Most instance of equisatisfiability -'~'- can be represented by equivalency in Isabelle/HOL.
  // Therefore, it should be possible to also use equivalency in a RESOLUTE based format.
  Proof handleApplyDef(Z3Proof node) {
    throw new UnsupportedOperationException();
  }

  // Z3_OP_PR_IFF_OEQ:
  //
  //       T1: (iff p q)
  //       [iff~ T1]: (~ p q)
  //
  // This rule does the opposite of what we are trying to do with the ~ operator. Skipping this
  // rule applicaiton should work. However, every instance of ~ later on should be replaced with
  // iff. In fact, replacing all ~ instances with iff might be desired.
  Proof handleIffOeq(Z3Proof node) {
    Z3Proof child = (Z3Proof) node.getChildren().toArray()[0];
    ResolutionProof resolutionProof = (ResolutionProof) handleNode(child);
    return resolutionProof;
  }

  // Z3_OP_PR_NNF_POS: Proof for a (positive) NNF step. Example:
  //
  //          T1: (not s_1) ~ r_1
  //          T2: (not s_2) ~ r_2
  //          T3: s_1 ~ r_1'
  //          T4: s_2 ~ r_2'                                r_2 => r_1     r_1  => r_2
  //          [nnf-pos T1 T2 T3 T4]: (~ (iff s_1 s_2) (and (or r_1 r_2') (or r_1' r_2)))
  //                                                              NOT r_2   not r_1
  //       The negation normal form steps NNF_POS and NNF_NEG are used in the following cases:
  //       (a) When creating the NNF of a positive force quantifier.
  //       The quantifier is retained (unless the bound variables are eliminated).
  //       Example
  //
  //            T1: q ~ q_new
  //            [nnf-pos T1]: (~ (forall (x T) q) (forall (x T) q_new))
  //
  //       (b) When recursively creating NNF over Boolean formulas, where the top-level
  //       connective is changed during NNF conversion. The relevant Boolean connectives
  //       for NNF_POS are 'implies', 'iff', 'xor', 'ite'.
  //       NNF_NEG furthermore handles the case where negation is pushed
  //       over Boolean connectives 'and' and 'or'.
  //
  // Possibly skip the rest of the tree and use oracle to introduce the equivalence this rule
  // proves.
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

  // Creates a subtree of resolution rule applications after creating the axiom needed to then
  // resolve each pivot.
  private ResolutionProof iterativeResolutionWithAxiom(Z3Proof node, ResAxiom axiom) {
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
