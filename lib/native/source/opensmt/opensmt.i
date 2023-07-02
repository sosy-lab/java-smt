// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

%module OsmtNative
%{
#include "include/opensmt/Opensmt.h"
%}

%include <stdint.i>

%include <std_string.i>
%include <std_vector.i>

%template(VectorInt)    std::vector<int>;
%template(VectorPTRef)  std::vector<PTRef>;
%template(VectorSRef)   std::vector<SRef>;
%template(VectorSymRef) std::vector<SymRef>;

%include <std_unique_ptr.i>

%unique_ptr(Model);
%unique_ptr(InterpolationContext);

%rename(OpenSmt) Opensmt;
%ignore Opensmt::Opensmt (opensmt_logic _logic, const char *name);
%ignore Opensmt::Opensmt (opensmt_logic _logic, const char *name, std::unique_ptr< SMTConfig > config);
%ignore Opensmt::getCUFLogic ();
%ignore Opensmt::getSolver ();
%extend Opensmt {
  %newobject Opensmt;
  Opensmt(opensmt_logic _logic, const char* name, bool prodInterpolants=false) {
    auto config = std::make_unique<SMTConfig>();
    const char* msg;
    bool ok = config->setOption(SMTConfig::o_produce_inter, SMTOption(prodInterpolants), msg);
    if (!ok) {
      throw std::runtime_error(msg);
    }
    else {
      return new Opensmt(_logic, name, std::move(config));
    }
  }
 }

%include "include/opensmt/Opensmt.h"

%ignore ASTType;
%ignore ASTNode;
%ignore ConfType;
%ignore ConfValue;
%ignore Info;

%ignore SMTOption::SMTOption(ASTNode const & n);
%ignore SMTOption::getValue() const;
   
%ignore SpType;
%ignore SpPref;
%ignore SpFormat;

%ignore ItpAlgorithm::operator==(const ItpAlgorithm& o) const;

%ignore itp_alg_mcmillan;
%ignore itp_alg_pudlak;
%ignore itp_alg_mcmillanp;
%ignore itp_alg_ps;
%ignore itp_alg_psw;
%ignore itp_alg_pss;
%extend ItpAlgorithm {
  static ItpAlgorithm getBoolMcmillan() {
    return itp_alg_mcmillan;
    }
  
  static ItpAlgorithm getBoolPudlak() {
    return itp_alg_pudlak;
    }
  
  static ItpAlgorithm getBoolMcmillanp() {
    return itp_alg_mcmillanp;
    }
  
  static ItpAlgorithm getBoolPs() {
    return itp_alg_ps;
    }
  
  static ItpAlgorithm getBoolPsw() {
    return itp_alg_psw;
    }
  
  static ItpAlgorithm getBoolPss() {
    return itp_alg_pss;
    }
 }

%ignore itp_euf_alg_strong;
%ignore itp_euf_alg_weak;
%ignore itp_euf_alg_random;
%extend ItpAlgorithm {
  static ItpAlgorithm getEufStrong() {
    return itp_euf_alg_strong;
  }
  
  static ItpAlgorithm getEufWeak() {
    return itp_euf_alg_weak;
  }
  
  static ItpAlgorithm getEufRandom() {
    return itp_euf_alg_random;
  }
 }

%ignore itp_lra_alg_strong;
%ignore itp_lra_alg_weak;
%ignore itp_lra_alg_factor;
%ignore itp_lra_alg_decomposing_strong;
%ignore itp_lra_alg_decomposing_weak;
%extend ItpAlgorithm {
  static ItpAlgorithm getLraStrong() {
    return itp_lra_alg_strong;
  }
  
  static ItpAlgorithm getLraWeak() {
    return itp_lra_alg_weak;
  }
  
  static ItpAlgorithm getLraFactor() {
    return itp_lra_alg_factor;
  }
  
  static ItpAlgorithm getLraDecomposingStrong() {
    return itp_lra_alg_decomposing_strong;
  }
  
  static ItpAlgorithm getLraDecomposingWeak() {
    return itp_lra_alg_decomposing_weak;
  }
  
  static const char* getLraFactor0() {
    return itp_lra_factor_0;
  }
 }

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
//%ignore SMTConfig::getRandomSeed () const;
%ignore SMTConfig::setProduceModels ();
//%ignore SMTConfig::setRandomSeed (int seed);
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

%include "include/opensmt/SMTConfig.h"

%ignore operator==(PTRef, PTRef);
%ignore operator!=(PTRef, PTRef);
%ignore operator>(PTRef, PTRef);
%ignore operator<(PTRef, PTRef);

%ignore PTRef_Undef;
%ignore PTRefHash;
%ignore PTRefPairHash;

%typemap(javacode) PTRef %{
  public boolean equals(Object object) {
    if(object instanceof $javaclassname) {
      PTRef that = ($javaclassname) object;
      return this.getX() == that.getX();
    }
    return false;
  }
  
  public int hashCode() {
    return Long.hashCode(this.getX());
  }
%}

%include "include/opensmt/PTRef.h"

%ignore PTLKey;
%ignore PTLHash;
%ignore PTId;

//%ignore Pterm::size () const;
%ignore Pterm::operator[] (int i) const;
//%ignore Pterm::symb () const;
%ignore Pterm::has_extra () const;
%ignore Pterm::reloced () const;
%ignore Pterm::relocation () const;
%ignore Pterm::relocate (PTRef t);
%ignore Pterm::type () const;
%ignore Pterm::type (uint32_t m);
%ignore Pterm::left_assoc () const;
%ignore Pterm::right_assoc () const;
%ignore Pterm::chainable () const;
%ignore Pterm::pairwise () const;
%ignore Pterm::noScoping () const;
%ignore Pterm::nargs () const;
%ignore Pterm::setLeftAssoc ();
%ignore Pterm::setRightAssoc ();
%ignore Pterm::setChainable ();
%ignore Pterm::setPairwise ();
%ignore Pterm::setNoScoping ();
%ignore Pterm::getId () const;
%ignore Pterm::setId (int i);
%ignore Pterm::shrink (int s);
%ignore Pterm::begin () const;
%ignore Pterm::end () const;
%extend Pterm {
  %newobject getArgs;
  std::vector<PTRef> getArgs() {
    std::vector<PTRef> args;
    for(auto i=0; i<$self->size(); i++)
      args.emplace_back($self->operator[](i));
    return args;
  }
 }

%ignore PtPair;
%ignore PtChild;
%ignore PtChildHash;
%ignore PtermAllocator;

%include "include/opensmt/Pterm.h"

//%ignore SSymRef;
%ignore SSymRef::operator= (uint32_t v);
%ignore operator== (SSymRef a1, SSymRef a2);
%ignore operator!= (SSymRef a1, SSymRef a2);

%ignore SSymRef_Undef;
%ignore SSymRefHash;

%typemap(javacode) SSymRef %{
  public boolean equals(Object object) {
    if(object instanceof $javaclassname) {
      SSymRef that = ($javaclassname) object;
      return this.getX() == that.getX();
    }
    return false;
  }
  
  public int hashCode() {
    return Long.hashCode(this.getX());
  }
%}

//%ignore SortSymbol;
%ignore SortSymbol::SortSymbol (std::string name_, unsigned int arity);
%ignore SortSymbol::SortSymbol (std::string name_, unsigned int arity, unsigned int flags);
%ignore SortSymbol::SortSymbol (SortSymbol &&);
%ignore SortSymbol::SortSymbol (SortSymbol const &);
//%ignore SortSymbol::isInternal () const;
//%ignore SortSymbol::name;
//%ignore SortSymbol::arity;
%ignore SortSymbol::flags;

//$ignore SRef;
%ignore SRef::operator= (uint32_t v);
%ignore operator== (SRef a1, SRef a2);
%ignore operator!= (SRef a1, SRef a2);

%ignore SRef_Undef;
%ignore SRef_Nil;

%ignore SRefHash;

%typemap(javacode) SRef %{
  public boolean equals(Object object) {
    if(object instanceof $javaclassname) {
      SRef that = ($javaclassname) object;
      return this.getX() == that.getX();
    }
    return false;
  }
  
  public int hashCode() {
    return Long.hashCode(this.getX());
  }
%}

//%ignore Sort;
%ignore Sort::Sort (SSymRef symRef_, sortid_t uniq_id_, vec< SRef > const &rest);
%ignore Sort::getId () const;
//%ignore Sort::getSymRef () const;
//%ignore Sort::getSize () const;
%ignore Sort::operator[] (uint32_t index) const;
%extend Sort {
  %newobject getArgs;
  std::vector<SRef> getArgs() {
    std::vector<SRef> args;
    for(auto i=0; i<$self->getSize(); i++)
      args.emplace_back($self->operator[](i));
    return args;
  }
 }

%ignore SortKey;
%ignore SortSymbolAllocator;

%ignore SortAllocator;

%include "include/opensmt/SSort.h"

%ignore SymRef::operator=(uint32_t v);
%ignore operator== (const SymRef& a1, const SymRef& a2);
%ignore operator!= (const SymRef& a1, const SymRef& a2);

%ignore SymRef_Undef;
%ignore SymRef_Nil;

%ignore SymRefHash;
%ignore Equal;

%typemap(javacode) SymRef %{
  public boolean equals(Object object) {
    if(object instanceof $javaclassname) {
      SymRef that = ($javaclassname) object;
      return this.getX() == that.getX();
    }
    return false;
  }
  
  public int hashCode() {
    return Long.hashCode(this.getX());
  }
%}

%include "include/opensmt/SymRef.h"

%ignore SymbolProperty;
%ignore SymbolConfig;
%ignore SymConf;
%ignore SymbolMatcher;

//%ignore Symbol;
//%ignore Symbol::size ();
%ignore Symbol::operator[] (int i) const;
%ignore Symbol::begin () const;
%ignore Symbol::end () const;
//%ignore Symbol::rsort () const;
%ignore Symbol::commutes () const;
%ignore Symbol::relocation () const;
%ignore Symbol::type () const;
%ignore Symbol::left_assoc () const;
%ignore Symbol::right_assoc () const;
%ignore Symbol::chainable () const;
%ignore Symbol::pairwise () const;
%ignore Symbol::noScoping () const;
%ignore Symbol::nargs () const;
%ignore Symbol::getId () const;
%ignore Symbol::setId (int i);
//%ignore Symbol::isInterpreted () const;
%ignore Symbol::matches (SymbolMatcher matcher) const;
%extend Symbol {
  %newobject getArgs;
  std::vector<SRef> getArgs() {
    std::vector<SRef> args;
    for(auto i=0; i<$self->size(); i++)
      args.emplace_back($self->operator[](i));
    return args;
  }
 }

%ignore SymbolAllocator;

%include "include/opensmt/Symbol.h"

%ignore FunctionSignature;

%ignore TemplateFunction::TemplateFunction (const std::string &name, const vec< PTRef > &args_, SRef ret_sort, PTRef tr_body);
%ignore TemplateFunction::TemplateFunction (FunctionSignature &&signature, PTRef body); 
%ignore TemplateFunction::TemplateFunction (const TemplateFunction &other);
%ignore TemplateFunction::TemplateFunction (TemplateFunction &&other);
%ignore TemplateFunction::operator= (TemplateFunction &&);
%ignore TemplateFunction::getArgs () const;
%extend TemplateFunction {
  TemplateFunction(const std::string &name, const std::vector< PTRef > &args_, SRef ret_sort, PTRef tr_body) {
    return new TemplateFunction(name, vec(args_), ret_sort, tr_body);
  }
  
  %newobject getArgs;
  std::vector<PTRef> getArgs() {
    std::vector<PTRef> res;
    for(PTRef a : $self->getArgs()) {
      res.emplace_back(a);
    }
    return res;
  }
}

%include "include/opensmt/FunctionTools.h"

%ignore Logic::propFormulasAppearingInUF;
%ignore Logic::tk_val_uf_default;
%ignore Logic::tk_val_bool_default;
%ignore Logic::tk_true;
%ignore Logic::tk_false;
%ignore Logic::tk_anon;
%ignore Logic::tk_uf_not;
%ignore Logic::tk_not;
%ignore Logic::tk_equals; 
%ignore Logic::tk_implies;
%ignore Logic::tk_and;
%ignore Logic::tk_or;
%ignore Logic::tk_xor;
%ignore Logic::tk_distinct;
%ignore Logic::tk_ite;
%ignore Logic::tk_indexed;
%ignore Logic::s_sort_bool;
%ignore Logic::s_ite_prefix;
%ignore Logic::s_framev_prefix;
%ignore Logic::s_abstract_value_prefix;
%ignore Logic::Logic (opensmt::Logic_t type);
%ignore Logic::getNumberOfTerms () const;
%ignore Logic::conjoinExtras (PTRef root);
%ignore Logic::getName () const;
%ignore Logic::getLogic () const;
%ignore Logic::hasUFs () const;
%ignore Logic::hasIntegers () const;
%ignore Logic::hasReals () const;
//%ignore Logic::getSortRef (PTRef tr) const; 
%ignore Logic::getSortRef (SymRef sr) const;
//%ignore Logic::printSort (SRef s) const;
//%ignore Logic::getSortSize (SRef s) const;
//%ignore Logic::getArraySort(SRef domain, SRef codomain);
//%ignore Logic::isArraySort (SRef sref) const;
%ignore Logic::hasArrays () const;
%ignore Logic::isArrayStore (SymRef) const;
%ignore Logic::isArraySelect (SymRef) const;
%ignore Logic::mkStore (vec< PTRef > &&);
%ignore Logic::mkSelect (vec< PTRef > &&);
%extend Logic {
  PTRef mkStore(PTRef array, PTRef index, PTRef value) {
    return $self->mkStore({array, index, value});
  }
  
  PTRef mkSelect(PTRef array, PTRef index) {
    return $self->mkSelect({array, index});
  }
 }
%ignore Logic::getUniqueArgSort (SymRef sr) const;
%ignore Logic::getUniqueArgSort (PTRef tr) const;
//%ignore Logic::getSym (const SymRef s) const;
%ignore Logic::getSym (const PTRef tr) const;
//%ignore Logic::getSymRef (const PTRef tr) const;
%ignore Logic::getSymName (const PTRef tr) const;
//%ignore Logic::getSymName (const SymRef s) const;
%ignore Logic::symNameToRef (const char *s);
%ignore Logic::hasSym (const char *s) const;
%ignore Logic::commutes (const SymRef s) const;
//%ignore Logic::getPterm (const PTRef tr);
%ignore Logic::getPterm (const PTRef tr) const;
%ignore Logic::getPtermIter ();
%ignore Logic::getTermMarks (PTId maxTermId) const;
%ignore Logic::getDefaultValue (const PTRef tr) const;
%ignore Logic::getDefaultValuePTRef (const PTRef tr) const;
%ignore Logic::getDefaultValuePTRef (const SRef sref) const;
%extend Logic {
  PTRef getDefaultValue(SRef sref) {
    return $self->getDefaultValuePTRef(sref);
  }
 }
%ignore Logic::mkUninterpFun (SymRef f, vec< PTRef > &&args);
%ignore Logic::mkUninterpFun (SymRef f, vec< PTRef > const &args);
%extend Logic {
  PTRef mkUninterpFun(SymRef f, std::vector<PTRef> const &args) {
    return $self->mkUninterpFun(f, vec(args));
  }
 }
%ignore Logic::mkAnd (vec< PTRef > &&);
%ignore Logic::mkAnd (vec< PTRef > const &args);
%extend Logic {
  PTRef mkAnd(std::vector<PTRef> const &args) {
    return $self->mkAnd(vec(args));
  }
 }
%ignore Logic::mkOr (vec< PTRef > &&);
%ignore Logic::mkOr (vec< PTRef > const &args);
%extend Logic {
  PTRef mkOr(std::vector<PTRef> const &args) {
    return $self->mkOr(vec(args));
  }
 }
%ignore Logic::mkXor (vec< PTRef > &&);
%ignore Logic::mkImpl (vec< PTRef > &&);
%extend Logic {
  PTRef mkImpl(std::vector<PTRef> const &args) {
    return $self->mkImpl(vec(args));
  }
 }
%ignore Logic::mkNot (vec< PTRef > &&);
%ignore Logic::mkIte (vec< PTRef > &&);
// %ignore Logic::mkIte (PTRef c, PTRef t, PTRef e);
%ignore Logic::mkEq (vec< PTRef > &&args);
%ignore Logic::mkEq (vec< PTRef > const &args);
%extend Logic {
  PTRef mkEq(std::vector<PTRef> const &args) {
    return $self->mkEq(vec(args));
  }
 }
%ignore Logic::mkDistinct (vec< PTRef > &&args);
%extend Logic {
  PTRef mkDistinct(std::vector<PTRef> const &args) {
    return $self->mkDistinct(vec(args));
  }
  
  PTRef mkDistinct(PTRef a, PTRef b) {
    std::vector<PTRef> args;
    args.emplace_back(a);
    args.emplace_back(b);
    return $self->mkDistinct(args);
  }
 }
//%ignore Logic::mkVar (SRef, const char *, bool isInterpreted=false);
%ignore Logic::mkUniqueAbstractValue (SRef);
%ignore Logic::mkConst (const char *); 
//%ignore Logic::mkConst (SRef, const char *);
%ignore Logic::declareFun (std::string const &fname, SRef rsort, vec< SRef > const &args, SymbolConfig const &symbolConfig);
%ignore Logic::declareFun (std::string const &fname, SRef rsort, vec< SRef > const &args);
%extend Logic {
  SymRef declareFun (std::string const &fname, SRef rsort, std::vector< SRef > const &args) {
    return $self->declareFun (fname, rsort, vec(args));
  }
}
%ignore Logic::declareFun_NoScoping (std::string const &s, SRef rsort, vec< SRef > const &args);
%ignore Logic::declareFun_NoScoping_LeftAssoc (std::string const &s, SRef rsort, vec< SRef > const &args);
%ignore Logic::declareFun_NoScoping_RightAssoc (std::string const &s, SRef rsort, vec< SRef > const &args);
%ignore Logic::declareFun_NoScoping_Chainable (std::string const &s, SRef rsort, vec< SRef > const &args);
%ignore Logic::declareFun_NoScoping_Pairwise (std::string const &s, SRef rsort, vec< SRef > const &args);
%ignore Logic::declareFun_Commutative_NoScoping_LeftAssoc (std::string const &s, SRef rsort, vec< SRef > const &args);
%ignore Logic::declareFun_Commutative_NoScoping_Chainable (std::string const &s, SRef rsort, vec< SRef > const &args);
%ignore Logic::declareFun_Commutative_NoScoping_Pairwise (std::string const &s, SRef rsort, vec< SRef > const &args);
%ignore Logic::declareFun_LeftAssoc (std::string const &s, SRef rsort, vec< SRef > const &args);
%ignore Logic::declareFun_RightAssoc (std::string const &s, SRef rsort, vec< SRef > const &args);
%ignore Logic::declareFun_Chainable (std::string const &s, SRef rsort, vec< SRef > const &args);
%ignore Logic::declareFun_Pairwise (std::string const &s, SRef rsort, vec< SRef > const &args);
%ignore Logic::instantiateFunctions (SRef);
%ignore Logic::instantiateArrayFunctions (SRef);
%ignore Logic::hasSortSymbol (SortSymbol const &); 
%ignore Logic::peekSortSymbol (SortSymbol const &, SSymRef &);
%ignore Logic::declareSortSymbol (SortSymbol symbol);
%ignore Logic::getSort (SSymRef, vec< SRef > &&args);
%ignore Logic::dumpHeaderToFile (std::ostream &dump_out) const;
%ignore Logic::dumpFormulaToFile (std::ostream &dump_out, PTRef formula, bool negate=false, bool toassert=true) const;
%ignore Logic::dumpChecksatToFile (std::ostream &dump_out) const;
%ignore Logic::dumpWithLets (std::ostream &out, PTRef formula) const;
%ignore Logic::dumpWithLets (PTRef formula) const;
%ignore Logic::instantiateFunctionTemplate (TemplateFunction const &tmplt, vec< PTRef > const &args);
%extend Logic {
  PTRef instantiateFunctionTemplate (TemplateFunction const &tmplt, std::vector< PTRef > const &args) {
    return $self->instantiateFunctionTemplate(tmplt, vec(args));
  }
 }
%ignore Logic::getSortSymIndexed () const;
%ignore Logic::getSym_true () const;
%ignore Logic::getSym_false () const;
%ignore Logic::getSym_and () const;
%ignore Logic::getSym_or () const;
%ignore Logic::getSym_xor () const;
%ignore Logic::getSym_not () const;
%ignore Logic::getSym_eq () const;
%ignore Logic::getSym_ite () const;
%ignore Logic::getSym_implies () const;
%ignore Logic::getSym_distinct () const;
%ignore Logic::getSym_uf_not () const;
//%ignore Logic::getSort_bool () const;
%extend Logic {
  bool isSortBool (SRef sort) {
    SRef sortBool = $self->getSort_bool();
    return sort == sortBool;
  }
 }
%ignore Logic::isEquality (SymRef tr) const;
//%ignore Logic::isEquality (PTRef tr) const;
%ignore Logic::isUFEquality (PTRef tr) const;
%ignore Logic::isTheoryEquality (PTRef tr) const;
%ignore Logic::isDisequality (SymRef tr) const;
//%ignore Logic::isDisequality (PTRef tr) const;
%ignore Logic::isIte (SymRef tr) const;
//%ignore Logic::isIte (PTRef tr) const;
%ignore Logic::isNonBoolIte (SymRef sr) const;
%ignore Logic::isNonBoolIte (PTRef tr) const;
%ignore Logic::isTheorySymbol (SymRef tr) const;
%ignore Logic::isTheoryTerm (PTRef tr) const;
%ignore Logic::isBooleanOperator (SymRef tr) const;
%ignore Logic::isBooleanOperator (PTRef tr) const;
%ignore Logic::isBuiltinSort (const SRef sr) const;
%ignore Logic::isBuiltinSortSym (const SSymRef ssr) const;
%ignore Logic::isBuiltinConstant (const SymRef sr) const;
%ignore Logic::isBuiltinConstant (const PTRef tr) const;
%ignore Logic::isBuiltinFunction (const SymRef sr) const;
%ignore Logic::isConstant (const SymRef sr) const;
//%ignore Logic::isConstant (PTRef tr) const;
%ignore Logic::yieldsSortUninterpreted (PTRef tr) const;
%ignore Logic::isUFSort (const SRef sr) const;
%ignore Logic::appearsInUF (PTRef tr) const; 
%ignore Logic::setAppearsInUF (PTRef tr);
%ignore Logic::getNestedBoolRoots (PTRef tr) const;
%ignore Logic::isVar (SymRef sr) const;
//%ignore Logic::isVar (PTRef tr) const;
%ignore Logic::isVarOrIte (SymRef sr) const;
%ignore Logic::isVarOrIte (PTRef tr) const;
%ignore Logic::isAtom (PTRef tr) const;
%ignore Logic::isBoolAtom (PTRef tr) const;
%ignore Logic::isInterpreted (SymRef sr) const;
%ignore Logic::isUP (PTRef) const;
//%ignore Logic::isUF (PTRef) const;
%ignore Logic::isUF (SymRef) const;
%ignore Logic::isIF (PTRef) const;
%ignore Logic::isIF (SymRef) const;
//%ignore Logic::isAnd (PTRef tr) const;
%ignore Logic::isAnd (SymRef sr) const;
//%ignore Logic::isOr (PTRef tr) const;
%ignore Logic::isOr (SymRef sr) const;
//%ignore Logic::isNot (PTRef tr) const;
%ignore Logic::isNot (SymRef sr) const;
%ignore Logic::isXor (SymRef sr) const;
//%ignore Logic::isXor (PTRef tr) const;
%ignore Logic::isImplies (SymRef sr) const;
//%ignore Logic::isImplies (PTRef tr) const;
%ignore Logic::isTrue (SymRef sr) const;
//%ignore Logic::isTrue (PTRef tr) const;
%ignore Logic::isFalse (SymRef sr) const;
//%ignore Logic::isFalse (PTRef tr) const;
%ignore Logic::isIff (SymRef sr) const;
//%ignore Logic::isIff (PTRef tr) const;
//%ignore Logic::hasSortBool (PTRef tr) const; 
%ignore Logic::hasSortBool (SymRef sr) const;
%ignore Logic::hasEquality (vec< PTRef > &args);
%ignore Logic::resolveTerm (const char *s, vec< PTRef > &&args, SRef sortRef=SRef_Undef, SymbolMatcher symbolMatcher=SymbolMatcher::Any);
%ignore Logic::insertTerm (SymRef sym, vec< PTRef > &&args);
%ignore Logic::insertTerm (SymRef sym, vec< PTRef > const &args);
%extend Logic {
  PTRef insertTerm (SymRef sym, std::vector<PTRef> const &args) {
    return $self->insertTerm(sym, vec(args));
  }
 }
%ignore Logic::getNewFacts (PTRef root, MapWithKeys< PTRef, lbool, PTRefHash > &facts);
%ignore Logic::retrieveSubstitutions (const vec< PtAsgn > &units);
%ignore Logic::substitutionsTransitiveClosure (SubstMap &substs);
%ignore Logic::contains (PTRef x, PTRef y);
%ignore Logic::learnEqTransitivity (PTRef);
%ignore Logic::removeAuxVars (PTRef tr);
%ignore Logic::hasQuotableChars (std::string const &name) const;
%ignore Logic::isReservedWord (std::string const &name) const;
%ignore Logic::isAmbiguousUninterpretedNullarySymbolName (std::string_view name) const;
%ignore Logic::protectName (std::string const &name, bool isInterpreted) const;
%ignore Logic::disambiguateName (std::string const &protectedName, SRef retSort, bool isNullary, bool isInterpreted) const;
%ignore Logic::protectName (SymRef sr) const;
%ignore Logic::printTerm_ (PTRef tr, bool l, bool s) const;
%ignore Logic::printTerm (PTRef tr) const;
%ignore Logic::printTerm (PTRef tr, bool l, bool s) const;
//%ignore Logic::pp (PTRef tr) const; 
%ignore Logic::printSym (SymRef sr) const;
%ignore Logic::termSort (vec< PTRef > &v) const;
%ignore Logic::purify (PTRef r, PTRef &p, lbool &sgn) const; 
%ignore Logic::collectStats (PTRef, int &n_of_conn, int &n_of_eq, int &n_of_uf, int &n_of_if);
%ignore Logic::typeCheck (SymRef sym, vec< PTRef > const &args, std::string &why) const;
%ignore Logic::verbose () const;

%include "include/opensmt/Logic.h"

%ignore LessThan_deepPTRef;
%ignore LANonLinearException;
%ignore ArithDivisionByZeroException;

%ignore ArithLogic::propFormulasAppearingInUF; 
%ignore ArithLogic::tk_val_uf_default;
%ignore ArithLogic::tk_val_bool_default;
%ignore ArithLogic::tk_true;
%ignore ArithLogic::tk_false;
%ignore ArithLogic::tk_anon;
%ignore ArithLogic::tk_uf_not;
%ignore ArithLogic::tk_not;
%ignore ArithLogic::tk_equals;
%ignore ArithLogic::tk_implies;
%ignore ArithLogic::tk_and;
%ignore ArithLogic::tk_or;
%ignore ArithLogic::tk_xor;
%ignore ArithLogic::tk_distinct;
%ignore ArithLogic::tk_ite;
%ignore ArithLogic::tk_indexed;
%ignore ArithLogic::s_sort_bool;
%ignore ArithLogic::s_ite_prefix;
%ignore ArithLogic::s_framev_prefix;
%ignore ArithLogic::s_abstract_value_prefix;
%ignore ArithLogic::ArithLogic (opensmt::Logic_t type);
%ignore ArithLogic::isBuiltinFunction (SymRef sr) const override;
%ignore ArithLogic::insertTerm (SymRef sym, vec< PTRef > &&terms) override;
//%ignore ArithLogic::getSort_real () const;
//%ignore ArithLogic::getSort_int () const;
%ignore ArithLogic::mkConst (const char *name) override;
//%ignore ArithLogic::mkConst (SRef s, const char *name) override;
%ignore ArithLogic::mkConst (SRef s, const std::string &name);
%ignore ArithLogic::mkConst (SRef s, opensmt::Number const &c);
%ignore ArithLogic::mkIntConst (opensmt::Number const &c);
%ignore ArithLogic::mkRealConst (opensmt::Number const &c);
%extend ArithLogic {
  PTRef mkIntConst(const std::string& c) {
    return $self->mkIntConst(FastRational(c.c_str()));
  }
  
  PTRef mkRealConst(const std::string& c) {
    return $self->mkRealConst(FastRational(c.c_str()));
  }
 }
//%ignore ArithLogic::mkIntVar (const char *name);
//%ignore ArithLogic::mkRealVar (const char *name);
%ignore ArithLogic::isBuiltinSort (SRef sr) const override;
%ignore ArithLogic::isBuiltinSortSym (SSymRef ssr) const override;
%ignore ArithLogic::isBuiltinConstant (SymRef sr) const override;
%ignore ArithLogic::isNumConst (SymRef sr) const;
//%ignore ArithLogic::isNumConst (PTRef tr) const;
%ignore ArithLogic::isIntConst (SymRef sr) const;
//%ignore ArithLogic::isIntConst (PTRef tr) const;
%ignore ArithLogic::isRealConst (SymRef sr) const;
//%ignore ArithLogic::isRealConst (PTRef tr) const;
%ignore ArithLogic::isNonNegNumConst (PTRef tr) const;
//%ignore ArithLogic::isSortInt (SRef sr) const;
//%ignore ArithLogic::isSortReal (SRef sr) const;
%ignore ArithLogic::isSortNum (SRef sr) const;
%ignore ArithLogic::yieldsSortInt (SymRef sr) const;
%ignore ArithLogic::yieldsSortInt (PTRef tr) const;
%ignore ArithLogic::yieldsSortReal (SymRef sr) const;
%ignore ArithLogic::yieldsSortReal (PTRef tr) const;
%ignore ArithLogic::yieldsSortNum (SymRef sr) const;
%ignore ArithLogic::yieldsSortNum (PTRef tr) const;
%ignore ArithLogic::getNumConst (PTRef tr) const;
%extend ArithLogic {
  std::string getNumConst (PTRef tr) {
    const FastRational& rat = $self->getNumConst(tr);
    return rat.get_str();
  }
 }
%ignore ArithLogic::isUFEquality (PTRef tr) const override;
%ignore ArithLogic::isAtom (PTRef tr) const override; 
%ignore ArithLogic::getDefaultValue (PTRef tr) const override;
%ignore ArithLogic::getDefaultValuePTRef (SRef sref) const override;
%ignore ArithLogic::get_sym_Int_TIMES () const;
%ignore ArithLogic::get_sym_Real_TIMES () const;
%ignore ArithLogic::get_sym_Int_DIV () const;
%ignore ArithLogic::get_sym_Int_MOD () const;
%ignore ArithLogic::get_sym_Real_DIV () const;
%ignore ArithLogic::get_sym_Int_MINUS () const;
%ignore ArithLogic::get_sym_Real_MINUS () const;
%ignore ArithLogic::get_sym_Real_PLUS () const;
%ignore ArithLogic::get_sym_Int_PLUS () const;
%ignore ArithLogic::get_sym_Int_NEG () const;
%ignore ArithLogic::get_sym_Int_LEQ () const;
%ignore ArithLogic::get_sym_Real_LEQ () const;
%ignore ArithLogic::getLeqForSort (SRef sr) const;
%ignore ArithLogic::get_sym_Int_GEQ () const;
%ignore ArithLogic::get_sym_Real_GEQ () const;
%ignore ArithLogic::get_sym_Int_LT () const;
%ignore ArithLogic::get_sym_Real_LT () const;
%ignore ArithLogic::get_sym_Int_GT () const;
%ignore ArithLogic::get_sym_Real_GT () const; 
%ignore ArithLogic::get_sym_Int_EQ () const;
%ignore ArithLogic::get_sym_Real_EQ () const;
%ignore ArithLogic::get_Sym_Int_ZERO () const;
%ignore ArithLogic::get_Sym_Real_ZERO () const;
%ignore ArithLogic::get_Sym_Int_ONE () const;
%ignore ArithLogic::get_Sym_Real_ONE () const;
%ignore ArithLogic::get_sym_Int_ITE () const;
%ignore ArithLogic::get_sym_Real_ITE () const;
%ignore ArithLogic::checkArithSortCompatible (vec< PTRef > const &args, SRef numSort) const;
%ignore ArithLogic::checkArithSortCompatible (vec< PTRef > const &args) const;
%ignore ArithLogic::checkHasReals () const;
%ignore ArithLogic::checkHasIntegers () const;
%ignore ArithLogic::isPlus (SymRef sr) const;
//%ignore ArithLogic::isPlus (PTRef tr) const;
%ignore ArithLogic::isIntPlus (PTRef tr) const;
%ignore ArithLogic::isRealPlus (PTRef tr) const;
%ignore ArithLogic::isIntPlus (SymRef sr) const;
%ignore ArithLogic::isRealPlus (SymRef sr) const;
%ignore ArithLogic::isMinus (SymRef sr) const;
%extend ArithLogic {
  bool isMinus(PTRef tr) const {
    return $self->isMinus($self->getPterm(tr).symb());
  }
 }
%ignore ArithLogic::isIntMinus (PTRef tr) const;
%ignore ArithLogic::isRealMinus (PTRef tr) const;
%ignore ArithLogic::isIntMinus (SymRef sr) const;
%ignore ArithLogic::isRealMinus (SymRef sr) const;
%ignore ArithLogic::isNeg (SymRef sr) const;
//%ignore ArithLogic::isNeg (PTRef tr) const;
%ignore ArithLogic::isIntNeg (PTRef tr) const;
%ignore ArithLogic::isRealNeg (PTRef tr) const;
%ignore ArithLogic::isIntNeg (SymRef sr) const;
%ignore ArithLogic::isRealNeg (SymRef sr) const;
%ignore ArithLogic::isTimes (SymRef sr) const;
//%ignore ArithLogic::isTimes (PTRef tr) const;
%ignore ArithLogic::isIntTimes (PTRef tr) const;
%ignore ArithLogic::isRealTimes (PTRef tr) const;
%ignore ArithLogic::isIntTimes (SymRef sr) const;
%ignore ArithLogic::isRealTimes (SymRef sr) const;
%ignore ArithLogic::isRealDiv (PTRef tr) const;
%ignore ArithLogic::isRealDiv (SymRef sr) const; 
%ignore ArithLogic::isIntDiv (PTRef tr) const;
%ignore ArithLogic::isIntDiv (SymRef sr) const;
%extend ArithLogic {
  bool isDiv(PTRef tr) const {
    return $self->isIntDiv(tr) || $self->isRealDiv(tr);
  }
 }
%ignore ArithLogic::isMod (SymRef sr) const;
%extend ArithLogic {
  bool isMod(PTRef tr) const {
    return $self->isMod($self->getPterm(tr).symb());
  }
 }
%ignore ArithLogic::isNumEq (SymRef sr) const;
%ignore ArithLogic::isNumEq (PTRef tr) const;
%ignore ArithLogic::isIntEq (PTRef tr) const;
%ignore ArithLogic::isRealEq (PTRef tr) const;
%ignore ArithLogic::isIntEq (SymRef sr) const;
%ignore ArithLogic::isRealEq (SymRef sr) const;
%ignore ArithLogic::isLeq (SymRef sr) const;
//%ignore ArithLogic::isLeq (PTRef tr) const;
%ignore ArithLogic::isIntLeq (PTRef tr) const;
%ignore ArithLogic::isRealLeq (PTRef tr) const;
%ignore ArithLogic::isIntLeq (SymRef sr) const;
%ignore ArithLogic::isRealLeq (SymRef sr) const;
%ignore ArithLogic::isLt (SymRef sr) const;
//%ignore ArithLogic::isLt (PTRef tr) const;
%ignore ArithLogic::isIntLt (PTRef tr) const;
%ignore ArithLogic::isRealLt (PTRef tr) const;
%ignore ArithLogic::isIntLt (SymRef sr) const;
%ignore ArithLogic::isRealLt (SymRef sr) const;
%ignore ArithLogic::isGeq (SymRef sr) const;
//%ignore ArithLogic::isGeq (PTRef tr) const;
%ignore ArithLogic::isIntGeq (PTRef tr) const;
%ignore ArithLogic::isRealGeq (PTRef tr) const;
%ignore ArithLogic::isIntGeq (SymRef sr) const; 
%ignore ArithLogic::isRealGeq (SymRef sr) const;
%ignore ArithLogic::isGt (SymRef sr) const;
//%ignore ArithLogic::isGt (PTRef tr) const;
%ignore ArithLogic::isIntGt (PTRef tr) const;
%ignore ArithLogic::isRealGt (PTRef tr) const;
%ignore ArithLogic::isIntGt (SymRef sr) const;
%ignore ArithLogic::isRealGt (SymRef sr) const;
%ignore ArithLogic::isNumVar (SymRef sr) const;
%ignore ArithLogic::isNumVar (PTRef tr) const;
%ignore ArithLogic::isNumVarLike (SymRef sr) const;
%ignore ArithLogic::isNumVarLike (PTRef tr) const;
%ignore ArithLogic::isZero (SymRef sr) const;
%ignore ArithLogic::isZero (PTRef tr) const; 
%ignore ArithLogic::isIntZero (PTRef tr) const;
%ignore ArithLogic::isRealZero (PTRef tr) const;
%ignore ArithLogic::isIntZero (SymRef sr) const;
%ignore ArithLogic::isRealZero (SymRef sr) const;
%ignore ArithLogic::isOne (PTRef tr) const;
%ignore ArithLogic::isIntOne (PTRef tr) const;
%ignore ArithLogic::isRealOne (PTRef tr) const;
%ignore ArithLogic::isIntOne (SymRef sr) const;
%ignore ArithLogic::isRealOne (SymRef sr) const;
%ignore ArithLogic::isNumTerm (PTRef tr) const;
//%ignore ArithLogic::getTerm_IntZero () const;
//%ignore ArithLogic::getTerm_RealZero () const;
//%ignore ArithLogic::getTerm_IntOne () const;
//%ignore ArithLogic::getTerm_RealOne () const;
//%ignore ArithLogic::getTerm_IntMinusOne () const;
//%ignore ArithLogic::getTerm_RealMinusOne () const;
%ignore ArithLogic::checkSortInt (PTRef tr);
%ignore ArithLogic::checkSortReal (PTRef tr);
%ignore ArithLogic::checkSortInt (vec< PTRef > const &args);
%ignore ArithLogic::checkSortReal (vec< PTRef > const &args);
%ignore ArithLogic::getPlusForSort (SRef sort) const;
%ignore ArithLogic::getTimesForSort (SRef sort) const;
%ignore ArithLogic::getMinusForSort (SRef sort) const;
%ignore ArithLogic::getZeroForSort (SRef sort) const;
%ignore ArithLogic::getOneForSort (SRef sort) const;
%ignore ArithLogic::getMinusOneForSort (SRef sort) const;
// PTRef 	mkNeg (PTRef tr)
%ignore ArithLogic::mkMinus (vec< PTRef > &&);
// PTRef 	mkMinus (PTRef a1, PTRef a2)
%ignore ArithLogic::mkMinus (vec< PTRef > const &args);
%ignore ArithLogic::mkPlus (vec< PTRef > &&);
// PTRef 	mkPlus (PTRef p1, PTRef p2)
%ignore ArithLogic::mkPlus (vec< PTRef > const &args);
%ignore ArithLogic::mkPlus (std::vector< PTRef > const &args);
%ignore ArithLogic::mkTimes (vec< PTRef > &&args);
// PTRef 	mkTimes (PTRef p1, PTRef p2)
%ignore ArithLogic::mkTimes (vec< PTRef > const &args);
%ignore ArithLogic::mkTimes (std::vector< PTRef > const &args);
%ignore ArithLogic::mkIntDiv (vec< PTRef > &&args);
// PTRef 	mkIntDiv (PTRef nom, PTRef den)
%ignore ArithLogic::mkIntDiv (vec< PTRef > const &args);
%ignore ArithLogic::mkRealDiv (vec< PTRef > &&args);
// mkRealDiv (PTRef nom, PTRef den)
%ignore ArithLogic::mkRealDiv (vec< PTRef > const &args);
%ignore ArithLogic::mkMod (vec< PTRef > &&args);
// PTRef 	mkMod (PTRef first, PTRef second)
%ignore ArithLogic::mkLeq (vec< PTRef > const &args);
// PTRef 	mkLeq (PTRef arg1, PTRef arg2)
%ignore ArithLogic::mkGeq (vec< PTRef > const &args);
// PTRef 	mkGeq (PTRef arg1, PTRef arg2)
%ignore ArithLogic::mkLt (vec< PTRef > const &args);
// PTRef 	mkLt (PTRef arg1, PTRef arg2) 
%ignore ArithLogic::mkGt (vec< PTRef > const &args);
// PTRef 	mkGt (PTRef arg1, PTRef arg2)
%ignore ArithLogic::isLinearTerm (PTRef tr) const;
%ignore ArithLogic::isLinearFactor (PTRef tr) const;
%ignore ArithLogic::getConstantAndFactors (PTRef sum) const;
%ignore ArithLogic::splitTermToVarAndConst (PTRef term) const;
%ignore ArithLogic::normalizeMul (PTRef mul);
%ignore ArithLogic::sumToNormalizedInequality (PTRef sum);
%ignore ArithLogic::sumToNormalizedEquality (PTRef sum);
%ignore ArithLogic::arithmeticElimination (vec< PTRef > const &top_level_arith, SubstMap &substitutions); 
%ignore ArithLogic::retrieveSubstitutions (vec< PtAsgn > const &facts) override;
%ignore ArithLogic::termSort (vec< PTRef > &v) const override;
%ignore ArithLogic::removeAuxVars (PTRef) override;
%ignore ArithLogic::printTerm_ (PTRef tr, bool ext, bool s) const override; 
%ignore ArithLogic::getConstantFromLeq (PTRef);
%ignore ArithLogic::getTermFromLeq (PTRef);
%ignore ArithLogic::leqToConstantAndTerm (PTRef);
%ignore ArithLogic::getNestedBoolRoots (PTRef) const override;

%include "include/opensmt/ArithLogic.h"

%ignore sstat::sstat(lbool l);
%ignore sstat::operator==(sstat s) const;
%ignore sstat::operator!=(sstat s) const;
%ignore sstat::getValue() const;
%ignore toSstat(int);
%extend sstat {
  bool isTrue() {
    return $self->getValue() == s_True.getValue();
  }
  
  bool isFalse() {
    return $self->getValue() == s_False.getValue();
  }
  
  bool isUndef() {
    return $self->getValue() == s_Undef.getValue();
  }
  
  bool isError() {
    return $self->getValue() == s_Error.getValue();
  }
 }
%ignore s_True;
%ignore s_False;
%ignore s_Undef;
%ignore s_Error;

//%ignore MainSolver::MainSolver (Logic &logic, SMTConfig &conf, std::string name);
%ignore MainSolver::MainSolver(std::unique_ptr<Theory>, std::unique_ptr<TermMapper>, std::unique_ptr<THandler>, std::unique_ptr<SimpSMTSolver>, Logic&, SMTConfig&, std::string);
%ignore MainSolver::getConfig();
%ignore MainSolver::getSMTSolver();
%ignore MainSolver::getSMTSolver() const;
%ignore MainSolver::getTHandler();
%ignore MainSolver::getLogic();
%ignore MainSolver::getTheory();
%ignore MainSolver::getTheory() const;
%ignore MainSolver::getPartitionManager();
//%ignore MainSolver::push(PTRef);
//%ignore MainSolver::push();
%ignore MainSolver::insertFormula(PTRef, char**);
//%ignore MainSolver::insertFormula(PTRef);;
%ignore MainSolver::initialize();
%ignore MainSolver::simplifyFormulas();
%ignore MainSolver::printFramesAsQuery() const;
%ignore MainSolver::solverEmpty() const;
%ignore MainSolver::writeSolverState_smtlib2(const char*, char**) const;
%ignore MainSolver::getTermValue(PTRef) const;
//%ignore MainSolver::stop();
%ignore MainSolver::createTheory(Logic&, SMTConfig&);
// %ignore MainSolver::getInterpolationContext ();

%include "include/opensmt/MainSolver.h"

%ignore Model::Model (Logic &logic, Evaluation basicEval, SymbolDefinition symbolDef); 
%ignore Model::Model (Logic &logic, Evaluation basicEval);
  
//%ignore Model::getDefinition (SymRef) const;
%ignore Model::getFormalArgBaseNameForSymbol (const Logic &logic, SymRef sr, const std::string &formalArgDefaultPrefix);

%include "include/opensmt/Model.h"

%ignore InterpolationContext::InterpolationContext (SMTConfig &c, Theory &th, TermMapper &termMapper, Proof const &t, PartitionManager &pmanager);
%ignore InterpolationContext::printProofDotty ();
%ignore InterpolationContext::getInterpolants (const std::vector< vec< int > > &partitions, vec< PTRef > &interpolants);
%ignore InterpolationContext::getSingleInterpolant (vec< PTRef > &interpolants, const ipartitions_t &A_mask);
%ignore InterpolationContext::getSingleInterpolant (std::vector< PTRef > &interpolants, const ipartitions_t &A_mask);
%ignore InterpolationContext::getPathInterpolants (vec< PTRef > &interpolants, const std::vector< ipartitions_t > &A_masks);
%extend InterpolationContext  {
  PTRef getSingleInterpolant (const std::vector<int>& partition) {
    std::vector<PTRef> interpolants;
    ipartitions_t mask;
    for(int i : partition)
      opensmt::setbit(mask, i);
    $self->getSingleInterpolant(interpolants, mask);
    return interpolants[0];
  }
 }

%include "include/opensmt/InterpolationContext.h"
