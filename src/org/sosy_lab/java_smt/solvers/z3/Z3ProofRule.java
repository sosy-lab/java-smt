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

import java.util.List;
import org.sosy_lab.java_smt.api.proofs.ProofRule;

// TODO correctly document the formula strings

/** Proof rules for Z3. These can be found in the Z3 API source code in the file Z3_api.h */
class Z3ProofRule implements ProofRule {

  enum Rule implements ProofRule {
    // Undefined proof object
    UNDEF("undef", "undefined proof object"),

    // Basic assertions
    TRUE("true", "proof for the expression 'true'"),

    ASSERTED("asserted", "(asserted p)"),

    GOAL("goal", "(goal p)"),

    // Logical inference rules
    MODUS_PONENS("modus_ponens", "(mp p (implies p q) q)"),

    REFLEXIVITY("reflexivity", "reflexivity (R t t), R is element of {=, ~, iff}"), // no antecendts

    SYMMETRY("symmetry", "symmetry (R t1 t2) (R t2 t1)"),

    TRANSITIVITY("transitivity", "trans (R t1 t2) (R t2 t3) (R t1 t3)"),

    TRANSITIVITY_STAR("transitivity*", "trans *(R t1 t2) ... (R t3 t4) (R t1 t4)"),

    MONOTONICITY(
        "monotonicity",
        "monotonicity (R t1 s1) ... (R tn sn) (R (f t1 ... tn) (f s1 ...  " + "sn))"),

    QUANT_INTRO("quant-intro", "quant-intro (~ p q) (~ (forall (x) p) (forall (x) q))"),

    BIND("bind", "(proof-bind f (forall (x) f))"),

    // Boolean and CNF transformations
    DISTRIBUTIVITY("distributivity", "(f g (= (f a (g b c)) (g (f a b) (f a c)))"), //

    // no antecedents
    AND_ELIM("and-elim", "and-elim (and p1 ... pn) pi"),

    NOT_OR_ELIM("not-or-elim", "not-or-elim (not (or p1 ... pn)) (not pi)"),

    // Rewriting and simplifications
    REWRITE("rewrite", "rewrite (R t s), R is element of {=, iff}"), // no antededents

    REWRITE_STAR("rewrite*", "rewrite* (= t1 t2) ... (= tn-1 tn) (= t1 tn)"),

    PULL_QUANT("pull_quant", "(= (f (forall x P(x)) R) (forall x (f P(x) R)))"),

    PUSH_QUANT(
        "push_quant",
        "(forall x (and P1(x) ... Pn(x))) (and (forall x P1(x)) ... (forall x Pn(x)))"),

    ELIM_UNUSED_VARS("elim_unused_vars", "(forall x y P(x)) (forall x P(x))"),

    DER("der", "(iff (forall x (or (not (= x t)) P(x))) P(t))"),

    QUANT_INST("quant_inst", "(or (not (forall x P(x))) P(a))"),

    // Natural deduction style
    HYPOTHESIS("hypothesis", "(hypothesis p)"),

    LEMMA("lemma", "(or (not p1) ... (not pn))"),

    UNIT_RESOLUTION(
        "unit_resolution", "(or p1 ... pn q1 ... qm) (not p1) ... (not pn) (or q1 ... qm)"),

    IFF_TRUE("iff_true", "(iff p true)"),

    IFF_FALSE("iff_false", "(iff p false)"),

    COMMUTATIVITY("commutativity", "(= (f a b) (f b a))"),

    // Tseitin-like axioms
    DEF_AXIOM("def_axiom", "Propositional tautologies (CNF conversion)"),

    // Clause manipulation rules
    ASSUMPTION_ADD("assumption_add", "(add_clause p)"),

    LEMMA_ADD("lemma_add", "(add_lemma p)"),

    REDUNDANT_DEL("redundant_del", "(delete_clause p)"),

    CLAUSE_TRAIL("clause_trail", "(clause_trail p)"),

    // Definitions and introduction rules
    DEF_INTRO("def_intro", "(= n e)"),

    APPLY_DEF("apply_def", "(~ p q)"),

    IFF_OEQ("iff_oeq", "(iff p q) (~ p q)"),

    // Negation Normal Form (NNF) transformations
    NNF_POS("nnf_pos", "(~ (iff p q) (and (or p (not q)) (or (not p) q)))"),

    NNF_NEG("nnf_neg", "(not (and p1 ... pn)) (or (not p1) ... (not pn))"),

    // Skolemization
    SKOLEMIZE("skolemize", "(~ (exists x P(x)) P(sk))"),

    // Theory reasoning
    MODUS_PONENS_OEQ("modus_ponens_oeq", "(mp~ p (~ p q) q)"),

    TH_LEMMA("th_lemma", "Theory-specific lemma"),

    HYPER_RESOLVE("hyper_resolve", "Hyper-resolution with multiple premises"),

    OPERATION("operation", "");

    private final String name;
    private final String formula;

    Rule(String name, String formula) {
      this.name = name;
      this.formula = formula;
    }

    @Override
    public String getName() {
      return name;
    }

    @Override
    public String getFormula() {
      return formula;
    }
  }

  static class Parameter<T> {
    private final T value;

    Parameter(T value) {
      this.value = value;
    }

    public T getValue() {
      return value;
    }
  }

  private final Rule rule;
  private final List<Parameter<?>> parameters;

  Z3ProofRule(Rule pRule, List<Parameter<?>> pParameters) {
    this.rule = pRule;
    this.parameters = pParameters;
  }

  @Override
  public String getName() {
    return rule.getName();
  }

  @Override
  public String getFormula() {
    return rule.getFormula();
  }

  public List<Parameter<?>> getParameters() {
    return List.copyOf(this.parameters);
  }
}
