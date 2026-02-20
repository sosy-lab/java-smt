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

import com.google.common.collect.ImmutableList;
import org.sosy_lab.java_smt.api.proofs.ProofRule;

/** Proof rules for Z3. These can be found in the Z3 API source code in the file Z3_api.h */
class Z3ProofRule implements ProofRule {

  enum Rule implements ProofRule {
    // Undefined proof object
    UNDEF("undef"),

    // Basic assertions
    TRUE("true"),

    ASSERTED("asserted"),

    GOAL("goal"),

    // Logical inference rules
    MODUS_PONENS("modus_ponens"),

    REFLEXIVITY("reflexivity"), // no antecendts

    SYMMETRY("symmetry"),

    TRANSITIVITY("transitivity"),

    TRANSITIVITY_STAR("transitivity*"),

    MONOTONICITY("monotonicity"),

    QUANT_INTRO("quant-intro"),

    BIND("bind"),

    // Boolean and CNF transformations
    DISTRIBUTIVITY("distributivity"), //

    // no antecedents
    AND_ELIM("and-elim"),

    NOT_OR_ELIM("not-or-elim"),

    // Rewriting and simplifications
    REWRITE("rewrite"), // no antededents

    REWRITE_STAR("rewrite*"),

    PULL_QUANT("pull_quant"),

    PUSH_QUANT("push_quant"),

    ELIM_UNUSED_VARS("elim_unused_vars"),

    DER("der"),

    QUANT_INST("quant_inst"),

    // Natural deduction style
    HYPOTHESIS("hypothesis"),

    LEMMA("lemma"),

    UNIT_RESOLUTION("unit_resolution"),

    IFF_TRUE("iff_true"),

    IFF_FALSE("iff_false"),

    COMMUTATIVITY("commutativity"),

    // Tseitin-like axioms
    DEF_AXIOM("def_axiom"),

    // Clause manipulation rules
    ASSUMPTION_ADD("assumption_add"),

    LEMMA_ADD("lemma_add"),

    REDUNDANT_DEL("redundant_del"),

    CLAUSE_TRAIL("clause_trail"),

    // Definitions and introduction rules
    DEF_INTRO("def_intro"),

    APPLY_DEF("apply_def"),

    IFF_OEQ("iff_oeq"),

    // Negation Normal Form (NNF) transformations
    NNF_POS("nnf_pos"),

    NNF_NEG("nnf_neg"),

    // Skolemization
    SKOLEMIZE("skolemize"),

    // Theory reasoning
    MODUS_PONENS_OEQ("modus_ponens_oeq"),

    TH_LEMMA("th_lemma"),

    HYPER_RESOLVE("hyper_resolve"),

    OPERATION("operation");

    private final String name;

    Rule(String pName) {
      name = pName;
    }

    @Override
    public String getName() {
      return name;
    }
  }

  static class Parameter<T> {
    private final T value;

    Parameter(T pValue) {
      value = pValue;
    }

    public T getValue() {
      return value;
    }
  }

  private final Rule rule;
  private final ImmutableList<Parameter<?>> parameters;

  Z3ProofRule(Rule pRule, ImmutableList<Parameter<?>> pParameters) {
    rule = pRule;
    parameters = ImmutableList.copyOf(pParameters);
  }

  @Override
  public String getName() {
    return rule.getName();
  }

  public ImmutableList<Parameter<?>> getParameters() {
    return parameters;
  }
}
