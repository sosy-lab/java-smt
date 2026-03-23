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

import java.util.HashMap;
import java.util.Locale;
import java.util.Map;
import org.sosy_lab.java_smt.api.proofs.ProofRule;

/**
 * A proof rule in the proof DAG of the proof format RESOLUTE used by SMTInterpol. See: <a
 * href="https://ultimate.informatik.uni-freiburg.de/smtinterpol/proof-format.html">RESOLUTE Proof
 * Format</a>
 *
 * <p>The conversion from other formats to RESOLUTE appears to be simple and as such, it is a good
 * candidate for a common proof format.
 *
 * @author Gabriel Carpio
 */
public final class ResProofRule {

  private static final Map<String, ResAxiom> RULE_MAP = new HashMap<>();

  private ResProofRule() {}

  static {
    for (ResAxiom rule : ResAxiom.values()) {
      RULE_MAP.put(rule.getName().toLowerCase(Locale.ENGLISH), rule);
    }
  }

  /**
   * Any operation that proves a term.
   */
  public enum ResAxiom implements ProofRule {
    // Resolution Rule
    RESOLUTION("res"),
    ASSUME("assume"),

    // Logical operators
    TRUE_POSITIVE("true+"),
    FALSE_NEGATIVE("false-"),
    NOT_POSITIVE("not+"),
    NOT_NEGATIVE("not-"),
    AND_POSITIVE("and+"),
    AND_NEGATIVE("and-"),
    OR_POSITIVE("or+"),
    OR_NEGATIVE("or-"),
    IMPLIES_POSITIVE("=>+"),
    IMPLIES_NEGATIVE("=>-"),
    EQUAL_POSITIVE1("=+1"),
    EQUAL_NEGATIVE1("=-1"),
    EQUAL_POSITIVE2("=+2"),
    EQUAL_NEGATIVE2("=-2"),
    XOR_POSITIVE("xor+"),
    XOR_NEGATIVE("xor-"),

    // Quantifiers
    FORALL_POSITIVE("forall+"),
    FORALL_NEGATIVE("forall-"),
    EXISTS_POSITIVE("exists+"),
    EXISTS_NEGATIVE("exists-"),

    // Equality axioms
    REFLEXIVITY("refl"),
    SYMMETRY("symm"),
    TRANSITIVITY("trans"),
    CONGRUENCE("cong"),
    EQUALITY_POSITIVE("=+"),
    EQUALITY_NEGATIVE("=-"),
    DISTINCT_POSITIVE("distinct+"),
    DISTINCT_NEGATIVE("distinct-"),

    // ITE, define-fun, annotations
    ITE1("ite1"),
    ITE2("ite2"),
    DEL("del!"),
    EXPAND("expand"),

    // Array Theory
    SELECTSTORE1("selectstore1"),
    SELECTSTORE2("selectstore2"),
    EXTDIFF("extdiff"),
    CONST("const"),

    // Linear Arithmetic
    POLY_ADD("poly+"),
    POLY_MUL("poly*"),
    TO_REAL("to_real"),
    FARKAS("farkas"),
    TRICHOTOMY("trichotomy"),
    TOTAL("total"),
    GT_DEF("gt_def"),
    GE_DEF("ge_def"),
    DIV_DEF("div_def"),
    NEG_DEF("neg_def"),
    NEG_DEF2("neg_def2"),
    ABS_DEF("abs_def"),
    TOTAL_INT("total-int"),
    TO_INT_LOW("to_int_low"),
    TO_INT_HIGH("to_int_high"),
    DIV_LOW("div_low"),
    DIV_HIGH("div_high"),
    MOD_DEF("mod_def"),
    DIVISIBLE_DEF("divisible_def"),
    EXPAND_IS_INT("expand_is_int"),

    // Data Types
    DT_PROJECT("dt_project"),
    DT_CONS("dt_cons"),
    DT_TEST_CONS("dt_test_cons"),
    DT_TEST_CONS_PRIME("dt_test_cons_prime"),
    DT_EXHAUST("dt_exhaust"),
    DT_ACYCLIC("dt_acyclic"),
    DT_MATCH("dt_match"),
    ORACLE("oracle");

    private final String name;

    ResAxiom(String pName) {
      name = pName;
    }

    @Override
    public String getName() {
      return name;
    }
  }

  /**
   * Retrieves a ProofRule by its name.
   *
   * @param name The name of the proof rule.
   * @return The matching ProofRule, or null if not found.
   */
  public static ResAxiom getFromName(String name) {
    return RULE_MAP.get(name.toLowerCase(Locale.ENGLISH));
  }
}
