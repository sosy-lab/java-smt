/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

package org.sosy_lab.java_smt.solvers.cvc5;

import java.util.HashMap;
import java.util.Map;
import org.sosy_lab.java_smt.ProofRuleRegistry;
import org.sosy_lab.java_smt.api.proofs.ProofRule;

// TODO: Properly include the formulas for the proof rules.
public enum CVC5ProofRule implements ProofRule {
  ASSUME("assume", ""),
  SCOPE("scope", ""),
  SUBS("subs", ""),
  MACRO_REWRITE("macro_rewrite", ""),
  EVALUATE("evaluate", ""),
  DISTINCT_VALUES("distinct_values", ""),
  ACI_NORM("aci_norm", ""),
  ABSORB("absorb", ""),
  MACRO_SR_EQ_INTRO("macro_sr_eq_intro", ""),
  MACRO_SR_PRED_INTRO("macro_sr_pred_intro", ""),
  MACRO_SR_PRED_ELIM("macro_sr_pred_elim", ""),
  MACRO_SR_PRED_TRANSFORM("macro_sr_pred_transform", ""),
  ENCODE_EQ_INTRO("encode_eq_intro", ""),
  DSL_REWRITE("dsl_rewrite", ""),
  THEORY_REWRITE("theory_rewrite", ""),
  ITE_EQ("ite_eq", ""),
  TRUST("trust", ""),
  TRUST_THEORY_REWRITE("trust_theory_rewrite", ""),
  SAT_REFUTATION("sat_refutation", ""),
  DRAT_REFUTATION("drat_refutation", ""),
  SAT_EXTERNAL_PROVE("sat_external_prove", ""),
  RESOLUTION("resolution", ""),
  CHAIN_RESOLUTION("chain_resolution", ""),
  FACTORING("factoring", ""),
  REORDERING("reordering", ""),
  MACRO_RESOLUTION("macro_resolution", ""),
  MACRO_RESOLUTION_TRUST("macro_resolution_trust", ""),
  SPLIT("split", ""),
  EQ_RESOLVE("eq_resolve", ""),
  MODUS_PONENS("modus_ponens", ""),
  NOT_NOT_ELIM("not_not_elim", ""),
  CONTRA("contra", ""),
  AND_ELIM("and_elim", ""),
  AND_INTRO("and_intro", ""),
  NOT_OR_ELIM("not_or_elim", ""),
  IMPLIES_ELIM("implies_elim", ""),
  NOT_IMPLIES_ELIM1("not_implies_elim1", ""),
  NOT_IMPLIES_ELIM2("not_implies_elim2", ""),
  EQUIV_ELIM1("equiv_elim1", ""),
  EQUIV_ELIM2("equiv_elim2", ""),
  NOT_EQUIV_ELIM1("not_equiv_elim1", ""),
  NOT_EQUIV_ELIM2("not_equiv_elim2", ""),
  XOR_ELIM1("xor_elim1", ""),
  XOR_ELIM2("xor_elim2", ""),
  NOT_XOR_ELIM1("not_xor_elim1", ""),
  NOT_XOR_ELIM2("not_xor_elim2", ""),
  ITE_ELIM1("ite_elim1", ""),
  ITE_ELIM2("ite_elim2", ""),
  NOT_ITE_ELIM1("not_ite_elim1", ""),
  NOT_ITE_ELIM2("not_ite_elim2", ""),
  NOT_AND("not_and", ""),
  CNF_AND_POS("cnf_and_pos", ""),
  CNF_AND_NEG("cnf_and_neg", ""),
  CNF_OR_POS("cnf_or_pos", ""),
  CNF_OR_NEG("cnf_or_neg", ""),
  CNF_IMPLIES_POS("cnf_implies_pos", ""),
  CNF_IMPLIES_NEG1("cnf_implies_neg1", ""),
  CNF_IMPLIES_NEG2("cnf_implies_neg2", ""),
  CNF_EQUIV_POS1("cnf_equiv_pos1", ""),
  CNF_EQUIV_POS2("cnf_equiv_pos2", ""),
  CNF_EQUIV_NEG1("cnf_equiv_neg1", ""),
  CNF_EQUIV_NEG2("cnf_equiv_neg2", ""),
  CNF_XOR_POS1("cnf_xor_pos1", ""),
  CNF_XOR_POS2("cnf_xor_pos2", ""),
  CNF_XOR_NEG1("cnf_xor_neg1", ""),
  CNF_XOR_NEG2("cnf_xor_neg2", ""),
  CNF_ITE_POS1("cnf_ite_pos1", ""),
  CNF_ITE_POS2("cnf_ite_pos2", ""),
  CNF_ITE_POS3("cnf_ite_pos3", ""),
  CNF_ITE_NEG1("cnf_ite_neg1", ""),
  CNF_ITE_NEG2("cnf_ite_neg2", ""),
  CNF_ITE_NEG3("cnf_ite_neg3", ""),
  REFL("refl", ""),
  SYMM("symm", ""),
  TRANS("trans", ""),
  CONG("cong", ""),
  NARY_CONG("nary_cong", ""),
  TRUE_INTRO("true_intro", ""),
  TRUE_ELIM("true_elim", ""),
  FALSE_INTRO("false_intro", ""),
  FALSE_ELIM("false_elim", ""),
  HO_APP_ENCODE("ho_app_encode", ""),
  HO_CONG("ho_cong", ""),
  ARRAYS_READ_OVER_WRITE("arrays_read_over_write", ""),
  ARRAYS_READ_OVER_WRITE_CONTRA("arrays_read_over_write_contra", ""),
  ARRAYS_READ_OVER_WRITE_1("arrays_read_over_write_1", ""),
  ARRAYS_EXT("arrays_ext", ""),
  MACRO_BV_BITBLAST("macro_bv_bitblast", ""),
  BV_BITBLAST_STEP("bv_bitblast_step", ""),
  BV_EAGER_ATOM("bv_eager_atom", ""),
  BV_POLY_NORM("bv_poly_norm", ""),
  BV_POLY_NORM_EQ("bv_poly_norm_eq", ""),
  DT_SPLIT("dt_split", ""),
  SKOLEM_INTRO("skolem_intro", ""),
  SKOLEMIZE("skolemize", ""),
  INSTANTIATE("instantiate", ""),
  ALPHA_EQUIV("alpha_equiv", ""),
  QUANT_VAR_REORDERING("quant_var_reordering", ""),
  SETS_SINGLETON_INJ("sets_singleton_inj", ""),
  SETS_EXT("sets_ext", ""),
  SETS_FILTER_UP("sets_filter_up", ""),
  SETS_FILTER_DOWN("sets_filter_down", ""),
  CONCAT_EQ("concat_eq", ""),
  CONCAT_UNIFY("concat_unify", ""),
  CONCAT_SPLIT("concat_split", ""),
  CONCAT_CSPLIT("concat_csplit", ""),
  CONCAT_LPROP("concat_lprop", ""),
  CONCAT_CPROP("concat_cprop", ""),
  STRING_DECOMPOSE("string_decompose", ""),
  STRING_LENGTH_POS("string_length_pos", ""),
  STRING_LENGTH_NON_EMPTY("string_length_non_empty", ""),
  STRING_REDUCTION("string_reduction", ""),
  STRING_EAGER_REDUCTION("string_eager_reduction", ""),
  RE_INTER("re_inter", ""),
  RE_CONCAT("re_concat", ""),
  RE_UNFOLD_POS("re_unfold_pos", ""),
  RE_UNFOLD_NEG("re_unfold_neg", ""),
  RE_UNFOLD_NEG_CONCAT_FIXED("re_unfold_neg_concat_fixed", ""),
  STRING_CODE_INJ("string_code_inj", ""),
  STRING_SEQ_UNIT_INJ("string_seq_unit_inj", ""),
  STRING_EXT("string_ext", ""),
  MACRO_STRING_INFERENCE("macro_string_inference", ""),
  MACRO_ARITH_SCALE_SUM_UB("macro_arith_scale_sum_ub", ""),
  ARITH_MULT_ABS_COMPARISON("arith_mult_abs_comparison", ""),
  ARITH_SUM_UB("arith_sum_ub", ""),
  INT_TIGHT_UB("int_tight_ub", ""),
  INT_TIGHT_LB("int_tight_lb", ""),
  ARITH_TRICHOTOMY("arith_trichotomy", ""),
  ARITH_REDUCTION("arith_reduction", ""),
  ARITH_POLY_NORM("arith_poly_norm", ""),
  ARITH_POLY_NORM_REL("arith_poly_norm_rel", ""),
  ARITH_MULT_SIGN("arith_mult_sign", ""),
  ARITH_MULT_POS("arith_mult_pos", ""),
  ARITH_MULT_NEG("arith_mult_neg", ""),
  ARITH_MULT_TANGENT("arith_mult_tangent", ""),
  ARITH_TRANS_PI("arith_trans_pi", ""),
  ARITH_TRANS_EXP_NEG("arith_trans_exp_neg", ""),
  ARITH_TRANS_EXP_POSITIVITY("arith_trans_exp_positivity", ""),
  ARITH_TRANS_EXP_SUPER_LIN("arith_trans_exp_super_lin", ""),
  ARITH_TRANS_EXP_ZERO("arith_trans_exp_zero", ""),
  ARITH_TRANS_EXP_APPROX_ABOVE_NEG("arith_trans_exp_approx_above_neg", ""),
  ARITH_TRANS_EXP_APPROX_ABOVE_POS("arith_trans_exp_approx_above_pos", ""),
  ARITH_TRANS_EXP_APPROX_BELOW("arith_trans_exp_approx_below", ""),
  ARITH_TRANS_SINE_BOUNDS("arith_trans_sine_bounds", ""),
  ARITH_TRANS_SINE_SHIFT("arith_trans_sine_shift", ""),
  ARITH_TRANS_SINE_SYMMETRY("arith_trans_sine_symmetry", ""),
  ARITH_TRANS_SINE_TANGENT_ZERO("arith_trans_sine_tangent_zero", ""),
  ARITH_TRANS_SINE_TANGENT_PI("arith_trans_sine_tangent_pi", ""),
  ARITH_TRANS_SINE_APPROX_ABOVE_NEG("arith_trans_sine_approx_above_neg", ""),
  ARITH_TRANS_SINE_APPROX_ABOVE_POS("arith_trans_sine_approx_above_pos", ""),
  ARITH_TRANS_SINE_APPROX_BELOW_NEG("arith_trans_sine_approx_below_neg", ""),
  ARITH_TRANS_SINE_APPROX_BELOW_POS("arith_trans_sine_approx_below_pos", ""),
  LFSC_RULE("lfsc_rule", ""),
  ALETHE_RULE("alethe_rule", ""),
  UNKNOWN("unknown", "");

  private final String name;
  private final String formula;

  CVC5ProofRule(String pName, String pFormula) {
    name = pName;
    formula = pFormula;
  }

  private static final Map<String, CVC5ProofRule> NAME_TO_RULE_MAP = new HashMap<>();

  static {
    for (CVC5ProofRule rule : values()) {
      ProofRuleRegistry.register(CVC5ProofRule.class, rule);
    }
  }

  @Override
  public String getName() {
    return "";
  }

  @Override
  public String getFormula() {
    return "";
  }
}
