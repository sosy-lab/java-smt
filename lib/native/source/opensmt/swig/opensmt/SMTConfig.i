// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

namespace opensmt {
%ignore ASTType;
%ignore ASTNode;
%ignore ConfType;
%ignore ConfValue;
%ignore Info;

%ignore SMTOption::SMTOption();
%ignore SMTOption::SMTOption(ASTNode const & n);
%extend SMTOption {
  %newobject SMTOption;
  SMTOption(bool b) {
    return new SMTOption(b);
  }
 }
%ignore SMTOption::getValue() const;

%ignore SpType;
%ignore SpPref;
%ignore SpFormat;

%ignore ItpAlgorithm;

%ignore itp_alg_mcmillan;
%ignore itp_alg_pudlak;
%ignore itp_alg_mcmillanp;
%ignore itp_alg_ps;
%ignore itp_alg_psw;
%ignore itp_alg_pss;

%ignore itp_euf_alg_strong;
%ignore itp_euf_alg_weak;
%ignore itp_euf_alg_random;

%ignore itp_lra_alg_strong;
%ignore itp_lra_alg_weak;
%ignore itp_lra_alg_factor;
%ignore itp_lra_alg_decomposing_strong;
%ignore itp_lra_alg_decomposing_weak;

%ignore itp_lra_factor_0;

%ignore operator==(const SpType& s1, const SpType& s2);
%ignore operator!=(const SpType& s1, const SpType& s2);
%ignore operator==(const SpPref& s1, const SpPref& s2);
%ignore operator!=(const SpPref& s1, const SpPref& s2);
%ignore operator==(const SpFormat& s1, const SpFormat& s2);
%ignore operator!=(const SpFormat& s1, const SpFormat& s2);

%ignore spts_lookahead;
%ignore spts_scatter;
%ignore spts_none;
%ignore spts_search_counter;
%ignore spts_time;
%ignore spprefs_tterm;
%ignore spprefs_blind;
%ignore spprefs_bterm;
%ignore spprefs_rand;
%ignore spprefs_noteq;
%ignore spprefs_eq;
%ignore spprefs_tterm_neq;
%ignore spformats_brief;
%ignore spformats_full;

%ignore spt_none;
%ignore spt_lookahead;
%ignore spt_scatter;

%ignore SpUnit;

%ignore sppref_tterm;
%ignore sppref_blind;
%ignore sppref_bterm;
%ignore sppref_rand;
%ignore sppref_undef;
%ignore sppref_noteq;
%ignore sppref_eq;
%ignore sppref_tterm_neq;

%ignore spformat_smt2;
%ignore spformat_osmt2;
%ignore spformat_brief;
%ignore spformat_full;

%ignore SMTConfig::SMTConfig (int argc, char *argv[]);
%ignore SMTConfig::setOption (const char *name, const SMTOption &value, const char *&msg);
%ignore SMTConfig::getOption (const char *name) const;
%ignore SMTConfig::setInfo (const char *name, const Info &value);
%ignore SMTConfig::getInfo (const char *name) const;
%ignore SMTConfig::initializeConfig ();
%ignore SMTConfig::parseConfig (char *);
%ignore SMTConfig::parseCMDLine (int argc, char *argv[]);
%ignore SMTConfig::printHelp ();
%ignore SMTConfig::printConfig (std::ostream &out);
%ignore SMTConfig::getStatsOut ();
%ignore SMTConfig::getRegularOut ();
%ignore SMTConfig::getDiagnosticOut ();
%ignore SMTConfig::getRandomSeed () const;
%ignore SMTConfig::setProduceModels ();
%ignore SMTConfig::setRandomSeed (int seed);
%ignore SMTConfig::setUsedForInitiliazation ();
%ignore SMTConfig::produceProof ();
%ignore SMTConfig::setTimeQueries ();
%ignore SMTConfig::timeQueries ();
%ignore SMTConfig::setReduction (int r);
%ignore SMTConfig::setReductionGraph (int r);
%ignore SMTConfig::setReductionLoops (int r);
%ignore SMTConfig::setInstanceName (const char *name);
%ignore SMTConfig::getBooleanInterpolationAlgorithm () const;
%ignore SMTConfig::getEUFInterpolationAlgorithm () const;
%ignore SMTConfig::getLRAInterpolationAlgorithm () const;
%ignore SMTConfig::getLRAStrengthFactor () const;
%ignore SMTConfig::getBooleanInterpolationAlgorithm () const;
%ignore SMTConfig::getEUFInterpolationAlgorithm () const;
%ignore SMTConfig::getLRAInterpolationAlgorithm () const;
%ignore SMTConfig::setBooleanInterpolationAlgorithm(ItpAlgorithm i);
%ignore SMTConfig::setEUFInterpolationAlgorithm(ItpAlgorithm i);
%ignore SMTConfig::setLRAInterpolationAlgorithm(ItpAlgorithm i);
%ignore SMTConfig::setLRAStrengthFactor(const char *factor);
%ignore SMTConfig::getInstanceName () const;
%ignore SMTConfig::setRegularOutputChannel (const char *attr);
%ignore SMTConfig::setDiagnosticOutputChannel (const char *attr);
%ignore SMTConfig::isIncremental () const;
%ignore SMTConfig::produce_models () const;
%ignore SMTConfig::produceStats () const;
%ignore SMTConfig::getStatsOut () const;
%ignore SMTConfig::sat_grow () const;
%ignore SMTConfig::sat_clause_lim () const;
%ignore SMTConfig::sat_subsumption_lim () const;
%ignore SMTConfig::sat_simp_garbage_frac () const;
%ignore SMTConfig::sat_use_asymm () const;
%ignore SMTConfig::sat_use_rcheck () const;
%ignore SMTConfig::sat_use_elim () const;
%ignore SMTConfig::sat_var_decay () const;
%ignore SMTConfig::sat_clause_decay () const;
%ignore SMTConfig::sat_random_var_freq () const;
%ignore SMTConfig::sat_random_seed () const;
%ignore SMTConfig::sat_luby_restart () const;
%ignore SMTConfig::sat_ccmin_mode () const;
%ignore SMTConfig::sat_rnd_pol () const;
%ignore SMTConfig::sat_rnd_init_act () const;
%ignore SMTConfig::sat_garbage_frac () const;
%ignore SMTConfig::sat_restart_first () const;
%ignore SMTConfig::sat_restart_inc () const;
%ignore SMTConfig::proof_interpolant_cnf () const;
%ignore SMTConfig::certify_inter () const;
%ignore SMTConfig::produce_inter () const;
%ignore SMTConfig::simplify_inter () const;
%ignore SMTConfig::proof_struct_hash () const;
%ignore SMTConfig::proof_num_graph_traversals () const;
%ignore SMTConfig::proof_red_trans () const;
%ignore SMTConfig::proof_rec_piv () const;
%ignore SMTConfig::proof_push_units () const;
%ignore SMTConfig::proof_transf_trav () const;
%ignore SMTConfig::proof_check () const;
%ignore SMTConfig::proof_multiple_inter () const;
%ignore SMTConfig::proof_alternative_inter () const;
%ignore SMTConfig::proof_reduce () const;
%ignore SMTConfig::itp_bool_alg () const;
%ignore SMTConfig::itp_euf_alg () const;
%ignore SMTConfig::itp_lra_alg () const;
%ignore SMTConfig::sat_dump_rnd_inter () const;
%ignore SMTConfig::declarations_are_global () const;
%ignore SMTConfig::sat_resource_units () const;
%ignore SMTConfig::respect_logic_partitioning_hints () const;
%ignore SMTConfig::sat_resource_limit () const;
%ignore SMTConfig::dump_state () const;
%ignore SMTConfig::output_dir () const;
%ignore SMTConfig::dump_only () const;
%ignore SMTConfig::dump_query () const;
%ignore SMTConfig::set_dump_query_name (const char *dump_query_name);
%ignore SMTConfig::dump_query_name () const;
%ignore SMTConfig::sat_dump_learnts () const;
%ignore SMTConfig::sat_split_test_cube_and_conquer () const;
%ignore SMTConfig::sat_split_type () const;
%ignore SMTConfig::sat_split_units () const;
%ignore SMTConfig::sat_split_inittune () const;
%ignore SMTConfig::sat_split_midtune () const;
%ignore SMTConfig::sat_split_num () const;
%ignore SMTConfig::sat_split_fixvars () const;
%ignore SMTConfig::sat_split_asap () const;
%ignore SMTConfig::sat_lookahead_split () const;
%ignore SMTConfig::sat_scatter_split () const;
%ignore SMTConfig::sat_pure_lookahead () const;
%ignore SMTConfig::lookahead_score_deep () const;
%ignore SMTConfig::sat_picky () const;
%ignore SMTConfig::randomize_lookahead () const;
%ignore SMTConfig::randomize_lookahead_bufsz () const;
%ignore SMTConfig::remove_symmetries () const;
%ignore SMTConfig::dryrun () const;
%ignore SMTConfig::set_dryrun (bool b);
%ignore SMTConfig::sat_split_preference () const;
%ignore SMTConfig::use_ghost_vars () const;
%ignore SMTConfig::do_substitutions () const;
%ignore SMTConfig::use_theory_polarity_suggestion () const;
%ignore SMTConfig::sat_picky_w () const;
%ignore SMTConfig::sat_solver_limit () const;
%ignore SMTConfig::sat_split_mode () const;
%ignore SMTConfig::verbosity () const;
%ignore SMTConfig::printSuccess () const;
%ignore SMTConfig::setSimplifyInterpolant (int val);
%ignore SMTConfig::getSimplifyInterpolant () const;
%ignore SMTConfig::status;
%ignore SMTConfig::print_stats;
%ignore SMTConfig::print_proofs_smtlib2;
%ignore SMTConfig::print_proofs_dotty;
%ignore SMTConfig::rocset;
%ignore SMTConfig::docset;
%ignore SMTConfig::dump_formula;
%ignore SMTConfig::certification_level;
%ignore SMTConfig::certifying_solver;
%ignore SMTConfig::sat_theory_polarity_suggestion;
%ignore SMTConfig::sat_initial_skip_step;
%ignore SMTConfig::sat_skip_step_factor;
%ignore SMTConfig::sat_use_luby_restart;
%ignore SMTConfig::sat_learn_up_to_size;
%ignore SMTConfig::sat_temporary_learn;
%ignore SMTConfig::sat_preprocess_booleans;
%ignore SMTConfig::sat_preprocess_theory;
%ignore SMTConfig::sat_centrality;
%ignore SMTConfig::sat_trade_off;
%ignore SMTConfig::sat_minimize_conflicts;
%ignore SMTConfig::sat_dump_cnf;
%ignore SMTConfig::sat_lazy_dtc;
%ignore SMTConfig::sat_lazy_dtc_burst;
%ignore SMTConfig::sat_reduce_proof;
%ignore SMTConfig::sat_reorder_pivots;
%ignore SMTConfig::sat_ratio_red_time_solv_time;
%ignore SMTConfig::sat_red_time;
%ignore SMTConfig::sat_num_glob_trans_loops;
%ignore SMTConfig::sat_remove_mixed;
%ignore SMTConfig::sat_propagate_small;
%ignore SMTConfig::sat_restart_learnt_thresh;
%ignore SMTConfig::sat_orig_thresh;
%ignore SMTConfig::proof_ratio_red_solv;
%ignore SMTConfig::proof_red_time;
%ignore SMTConfig::proof_reorder_pivots;
%ignore SMTConfig::proof_reduce_while_reordering;
%ignore SMTConfig::proof_random_context_analysis;
%ignore SMTConfig::proof_random_swap_application;
%ignore SMTConfig::proof_remove_mixed;
%ignore SMTConfig::proof_certify_inter;
%ignore SMTConfig::proof_random_seed;
%ignore SMTConfig::proof_switch_to_rp_hash;
%ignore SMTConfig::proof_trans_strength;
%ignore SMTConfig::uf_disable;
%ignore SMTConfig::cuf_bitwidth;
%ignore SMTConfig::bv_disable;
%ignore SMTConfig::dl_disable;
%ignore SMTConfig::lra_disable;
%ignore SMTConfig::lra_poly_deduct_size;
%ignore SMTConfig::lra_trade_off;
%ignore SMTConfig::lra_integer_solver;
%ignore SMTConfig::lra_check_on_assert;
%ignore SMTConfig::o_incremental;
%ignore SMTConfig::o_verbosity;
%ignore SMTConfig::o_produce_stats;
%ignore SMTConfig::o_stats_out;
%ignore SMTConfig::o_random_seed;
%ignore SMTConfig::o_grow;
%ignore SMTConfig::o_clause_lim;
%ignore SMTConfig::o_subsumption_lim;
%ignore SMTConfig::o_simp_garbage_frac;
%ignore SMTConfig::o_use_asymm;
%ignore SMTConfig::o_use_rcheck;
%ignore SMTConfig::o_use_elim;
%ignore SMTConfig::o_var_decay;
%ignore SMTConfig::o_clause_decay;
%ignore SMTConfig::o_random_var_freq;
%ignore SMTConfig::o_luby_restart;
%ignore SMTConfig::o_ccmin_mode;
%ignore SMTConfig::o_rnd_pol;
%ignore SMTConfig::o_rnd_init_act;
%ignore SMTConfig::o_garbage_frac;
%ignore SMTConfig::o_restart_first;
%ignore SMTConfig::o_restart_inc;
%ignore SMTConfig::o_produce_proofs;
%ignore SMTConfig::o_produce_inter;
%ignore SMTConfig::o_certify_inter;
%ignore SMTConfig::o_simplify_inter;
%ignore SMTConfig::o_interpolant_cnf;
%ignore SMTConfig::o_proof_struct_hash;
%ignore SMTConfig::o_proof_num_graph_traversals;
%ignore SMTConfig::o_proof_red_trans;
%ignore SMTConfig::o_proof_rec_piv;
%ignore SMTConfig::o_proof_push_units;
%ignore SMTConfig::o_proof_transf_trav;
%ignore SMTConfig::o_proof_check;
%ignore SMTConfig::o_proof_multiple_inter;
%ignore SMTConfig::o_proof_alternative_inter;
%ignore SMTConfig::o_proof_reduce;
%ignore SMTConfig::o_itp_bool_alg;
%ignore SMTConfig::o_itp_euf_alg;
%ignore SMTConfig::o_itp_lra_alg;
%ignore SMTConfig::o_itp_lra_factor;
%ignore SMTConfig::o_sat_dump_rnd_inter;
%ignore SMTConfig::o_sat_resource_units;
%ignore SMTConfig::o_sat_resource_limit;
%ignore SMTConfig::o_dump_state;
%ignore SMTConfig::o_time_queries;
%ignore SMTConfig::o_inst_name;
%ignore SMTConfig::o_dump_only;
%ignore SMTConfig::o_dump_mode;
%ignore SMTConfig::o_dump_query;
%ignore SMTConfig::o_dump_query_name;
%ignore SMTConfig::o_sat_dump_learnts;
%ignore SMTConfig::o_sat_split_type;
%ignore SMTConfig::o_sat_split_inittune;
%ignore SMTConfig::o_sat_split_midtune;
%ignore SMTConfig::o_sat_split_num;
%ignore SMTConfig::o_sat_split_fix_vars;
%ignore SMTConfig::o_sat_split_asap;
%ignore SMTConfig::o_sat_scatter_split;
%ignore SMTConfig::o_sat_lookahead_split;
%ignore SMTConfig::o_sat_pure_lookahead;
%ignore SMTConfig::o_lookahead_score_deep;
%ignore SMTConfig::o_sat_picky;
%ignore SMTConfig::o_sat_picky_w;
%ignore SMTConfig::o_sat_split_units;
%ignore SMTConfig::o_sat_split_preference;
%ignore SMTConfig::o_sat_split_test_cube_and_conquer;
%ignore SMTConfig::o_sat_split_randomize_lookahead;
%ignore SMTConfig::o_sat_split_randomize_lookahead_buf;
%ignore SMTConfig::o_produce_models;
%ignore SMTConfig::o_sat_remove_symmetries;
%ignore SMTConfig::o_dryrun;
%ignore SMTConfig::o_do_substitutions;
%ignore SMTConfig::o_respect_logic_partitioning_hints;
%ignore SMTConfig::o_output_dir;
%ignore SMTConfig::o_ghost_vars;
%ignore SMTConfig::o_sat_solver_limit;
%ignore SMTConfig::o_global_declarations;
%ignore SMTConfig::o_sat_split_mode;
%ignore SMTConfig::server_host;
%ignore SMTConfig::server_port;
%ignore SMTConfig::database_host;
%ignore SMTConfig::database_port;
%extend SMTConfig {
  void setOption(const char* option, SMTOption& value) {
    const char* msg;
    bool ok = $self->setOption(option, value, msg);
    if (!ok) {
      throw std::runtime_error(msg);
    }
  }
 }
}

%include "include/opensmt/options/SMTConfig.h"
