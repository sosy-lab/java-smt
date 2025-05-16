/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt;

import com.google.common.base.Preconditions;
import java.util.HashMap;
import java.util.Locale;
import java.util.Map;
import org.sosy_lab.java_smt.api.proofs.ProofRule;

/**
 * A proof rule in the proof DAG of the proof format RESOLUTE used by SMTInterpol. See: <a
 * href="https://ultimate.informatik.uni-freiburg.de/smtinterpol/proof-format.html">...</a>
 *
 * <p>The conversion from other formats to RESOLUTE appears to be simple and as such, it is a good
 * candidate for a common proof format.
 *
 * @author Gabriel Carpio
 */
public final class ResProofRule {

  private static final Map<String, ResAxiom> RULE_MAP = new HashMap<>();

  private ResProofRule() {
    // prevent instantiation
  }

  static {
    for (ResAxiom rule : ResAxiom.values()) {
      RULE_MAP.put(rule.getName().toLowerCase(Locale.ENGLISH), rule);
    }
  }

  /** Any operation that proves a term. */
  public enum ResAxiom implements ProofRule {
    // Resolution Rule
    RESOLUTION("res", "(res t proof1 proof2)"),
    ASSUME("assume", "(assume t)"),
    // Logical operators
    TRUE_POSITIVE("true+", "(+ true)"),
    FALSE_NEGATIVE("false-", "(- false)"),
    NOT_POSITIVE("not+", "(+ (not p0) + p0)"),
    NOT_NEGATIVE("not-", "(- (not p0) - p0)"),
    AND_POSITIVE("and+", "(+ (and p0 … pn) - p0 … - pn)"),
    AND_NEGATIVE("and-", "(- (and p0 … pn) + pi)"),
    OR_POSITIVE("or+", "(+ (or p0 … pn) - pi)"),
    OR_NEGATIVE("or-", "(- (or p0 … pn) + p0 … + pn)"),
    IMPLIES_POSITIVE("=>+", "(+ (=> p0 … pn) +/- pi)"),
    IMPLIES_NEGATIVE("=>-", "(- (=> p0 … pn) - p0 … + pn)"),
    EQUAL_POSITIVE1("=+1", "(+ (= p0 p1) + p0 + p1)"),
    EQUAL_NEGATIVE1("=-1", "(- (= p0 p1) + p0 - p1)"),
    EQUAL_POSITIVE2("=+2", "(+ (= p0 p1) - p0 - p1)"),
    EQUAL_NEGATIVE2("=-2", "(- (= p0 p1) - p0 + p1)"),
    XOR_POSITIVE("xor+", "(+(xor l1) +(xor l2) -(xor l3))"),
    XOR_NEGATIVE("xor-", "(-(xor l1) -(xor l2) -(xor l3))"),

    // Quantifiers
    FORALL_POSITIVE("forall+", "(+ (forall x (F x)) - (F (choose x (F x))))"),
    FORALL_NEGATIVE("forall-", "(- (forall x (F x)) + (F t))"),
    EXISTS_POSITIVE("exists+", "(+ (exists x (F x)) - (F t))"),
    EXISTS_NEGATIVE("exists-", "(- (exists x (F x)) + (F (choose x (F x))))"),

    // Equality axioms
    REFLEXIVITY("refl", "(+ (= t t))"),
    SYMMETRY("symm", "(+(= t0 t1) -(= t1 t0))"),
    TRANSITIVITY("trans", "(+(= t0 tn) -(= t0 t1) … -(= tn-1 tn))"),
    CONGRUENCE("cong", "(+(= (f t0 … tn) (f t0' … tn')) -(= t0 t0') … -(= tn tn'))"),
    EQUALITY_POSITIVE("=+", "(+ (= t0 … tn) -(= t0 t1) … -(= tn-1 tn))"),
    EQUALITY_NEGATIVE("=-", "(- (= t0 … tn) +(= ti tj))"),
    DISTINCT_POSITIVE("distinct+", "(+ (distinct t0 … tn) +(= t0 t1) … +(= t0 tn) … +(= tn-1 tn))"),
    DISTINCT_NEGATIVE("distinct-", "(- (distinct t0 … tn) -(= ti tj))"),

    // ITE, define-fun, annotations
    ITE1("ite1", "(+(= (ite t0 t1 t2) t1) - t0)"),
    ITE2("ite2", "(+(= (ite t0 t1 t2) t2) + t0)"),
    DEL("del!", "(+(= (! t :annotation…) t))"),
    EXPAND("expand", "(+(= (f t0 … tn) (let ((x0 t0)…(xn tn)) d)))"),

    // Array Theory
    SELECTSTORE1("selectstore1", "(+ (= (select (store a i v) i) v))"),
    SELECTSTORE2("selectstore2", "(+ (= (select (store a i v) j) (select a j)) (= i j))"),
    EXTDIFF("extdiff", "(+ (= a b) (- (= (select a (@diff a b)) (select b (@diff a b)))))"),
    CONST("const", "(+ (= (select (@const v) i) v))"),

    // Linear Arithmetic
    POLY_ADD("poly+", "(+ (= (+ a1 ... an) a))"),
    POLY_MUL("poly*", "(+ (= (* a1 ... an) a))"),
    TO_REAL("to_real", "(+ (= (to_real a) a'))"),
    FARKAS("farkas", "(- (<=? a1 b1) ... - (<=? an bn))"),
    TRICHOTOMY("trichotomy", "(+ (< a b) (= a b) (< b a))"),
    TOTAL("total", "(+ (<= a b) (< b a))"),
    GT_DEF("gt_def", "(+ (= (> a b) (< b a)))"),
    GE_DEF("ge_def", "(+ (= (>= a b) (<= b a)))"),
    DIV_DEF("div_def", "(+ (= a (* b1 ... bn (/ a b1 ... bn))) (= b1 0) ... (= bn 0))"),
    NEG_DEF("neg_def", "(+ (= (- a) (* (- 1) a)))"),
    NEG_DEF2("neg_def2", "(+ (= (- a b1 ... bn) (+ a (* (- 1) b1)) ... (* (- 1) bn)))"),
    ABS_DEF("abs_def", "(+ (= (abs x) (ite (< x 0) (- x) x)))"),
    TOTAL_INT("total_int", "(+ (<= a c) (<= (c+1) a))"),
    TO_INT_LOW("to_int_low", "(+ (<= (to_real (to_int x)) x))"),
    TO_INT_HIGH("to_int_high", "(+ (< x (+ (to_real (to_int x)) 1.0)))"),
    DIV_LOW("div_low", "(+ (<= (* d (div x d)) x) (= d 0))"),
    DIV_HIGH("div_high", "(+ (< x (+ (* d (div x d)) (abs d))) (= d 0))"),
    MOD_DEF("mod_def", "(+ (= (mod x d) (- x (* d (div x d)))) (= d 0))"),
    DIVISIBLE_DEF("divisible_def", "(+ (= ((_ divisible c) x) (= x (* c (div x c)))))"),
    EXPAND_IS_INT("expand_is_int", "(+ (= (is_int x) (= x (to_real (to_int x)))))"),

    // Data Types
    DT_PROJECT("dt_project", "(= (seli (cons a1 ... an)) ai)"),
    DT_CONS("dt_cons", "(~ ((_ is cons) x), (= (cons (sel1 x) ... (seln x)) x))"),
    DT_TEST_CONS("dt_test_cons", "((_ is cons) (cons a1 ... an))"),
    DT_TEST_CONS_PRIME("dt_test_cons_prime", "(~ ((_ is cons') (cons a1 ... an)))"),
    DT_EXHAUST("dt_exhaust", "((_ is cons1) x), ..., ((_ is consn) x)"),
    DT_ACYCLIC("dt_acyclic", "(~ (= (cons ... x ...) x))"),
    DT_MATCH(
        "dt_match",
        "(= (match t ((p1 x1) c1) ...) (ite ((_ is p1) t) (let (x1 (sel1 t)) c1) ...))");

    private final String name;
    private final String formula;

    ResAxiom(String pName, String pFormula) {
      name = pName;
      formula = pFormula;
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

  /**
   * Retrieves a ProofRule by its name.
   *
   * @param name The name of the proof rule.
   * @return The matching ProofRule.
   * @throws NullPointerException if the name is null.
   * @throws IllegalArgumentException if the name does not match any rule.
   */
  public static ResAxiom getFromName(String name) {
    ResAxiom rule = RULE_MAP.get(name.toLowerCase(Locale.ENGLISH));
    return rule;
  }
}
