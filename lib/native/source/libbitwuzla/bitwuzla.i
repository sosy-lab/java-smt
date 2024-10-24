// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

%module(directors="1") BitwuzlaNative
%{
#include <bitwuzla/cpp/bitwuzla.h>
#include <bitwuzla/cpp/parser.h>

#include <string>
#include <sstream>

#include <cassert>
%}

%include <stdint.i>
%include <std_string.i>

%include <std_vector.i>
%template(Vector_Int) std::vector<int>;
%template(Vector_String) std::vector<std::string>;
%template(Vector_Term) std::vector<bitwuzla::Term>;
%template(Vector_Sort) std::vector<bitwuzla::Sort>;

%include <std_unordered_map.i>
%template(Map_TermTerm) std::unordered_map<bitwuzla::Term, bitwuzla::Term>;

%include <std_shared_ptr.i>
%shared_ptr(bitwuzla::Bitwuzla);

%exception {
  try {
    $action
  } catch(bitwuzla::Exception& e) {
    jclass exceptionType = jenv->FindClass("java/lang/IllegalArgumentException");
    jenv->ThrowNew(exceptionType, e.what());
    return $null;
  }
}

namespace std {
%ignore to_string(bitwuzla::Kind kind);
%ignore to_string(bitwuzla::RoundingMode rm);
%ignore to_string(bitwuzla::Result result);
}

%include "include/bitwuzla/enums.h"
%include "include/bitwuzla/option.h"

namespace bitwuzla {
/** Output streams */
%ignore set_bv_format;
%ignore operator<< (std::ostream &ostream, const set_bv_format &f);
%ignore operator<< (std::ostream &out, Result result);
%ignore operator<< (std::ostream &out, Kind kind);
%ignore operator<< (std::ostream &out, RoundingMode rm);

/** Exception */
%ignore Exception;

/** Options */
%ignore Options::operator= (const Options &options);
%ignore Options::set (Option option, const char *mode);
%ignore Options::set (Option option, uint64_t value);
%extend Options {
  void set(Option option, int value) {
    $self->set(option, value);
  }
}

/** OptionInfo */
%ignore OptionInfo;

/** Term */
%rename(get) Term::operator[];
%rename(toString) Term::str;

%ignore Term::id() const;
%extend Term {
  int id() {
    return (int) $self->id();
  }
}

%ignore Term::indices () const;
%extend Term {
  std::vector<int> indices() {
    std::vector<int> result;
    for(auto v : $self->indices()) {
      result.emplace_back(v);
    }
    return result;
  }
}

%ignore Term::symbol () const;
%exception Term::symbol {
  try {
    $action
  } catch(std::bad_optional_access& e) {
    return $null;
  }
}
%extend Term {
  std::string symbol() {
    return $self->symbol().value();
  }
}

%ignore Term::value() const;
%extend Term {
  bool to_bool() {
    assert($self->is_value() && $self->sort().is_bool());
    return $self->value<bool>();
  }

  bitwuzla::RoundingMode to_rm() {
    assert($self->is_value() && $self->sort().is_rm());
    return $self->value<bitwuzla::RoundingMode>();
  }

  std::string to_bv() {
    assert($self->is_value() && ($self->sort().is_bv() || $self->sort().is_fp()));
    return $self->value<std::string>();
  }
}

%ignore operator==(const Term &a, const Term &b);
%ignore operator!=(const Term &a, const Term &b);
%ignore operator<< (std::ostream &out, const Sort &sort);
%extend Term {
  int hashCode() {
    std::hash<bitwuzla::Term> f;
    return (int) f(*$self);
  }

  bool isEqual(Term other) {
    return operator==(*$self, other);
  }
}

%typemap(javacode) Term %{
  public boolean equals(Object object) {
    if(object instanceof $javaclassname) {
      Term that = ($javaclassname) object;
      return this.isEqual(that);
    }
    return false;
  }
%}

/** Sort */
%rename(toString) Sort::str;

%ignore Sort::uninterpreted_symbol() const;
%ignore Sort::is_uninterpreted() const;

%ignore Sort::id() const;
%extend Sort {
  int id() {
    return (int) $self->id();
  }
}

%ignore Sort::bv_size() const;
%extend Sort {
  int bv_size() {
    return (int) $self->bv_size();
  }
}

%ignore Sort::fp_exp_size() const;
%ignore Sort::fp_sig_size() const;
%extend Sort {
  int fp_exp_size() {
    return (int) $self->fp_exp_size();
  }
  int fp_sig_size() {
    return (int) $self->fp_sig_size();
  }
}

%ignore Sort::fun_arity() const;
%extend Sort {
  int fun_arity() {
    return (int) $self->fun_arity();
  }
}

%ignore operator==(const Sort &a, const Sort &b);
%ignore operator!=(const Sort &a, const Sort &b);
%ignore operator<< (std::ostream &out, const Sort &sort);
%extend Sort {
  int hashCode() {
    std::hash<bitwuzla::Sort> f;
    return (int) f(*$self);
  }
  bool isEqual(Sort other) {
    return operator==(*$self, other);
  }
}

%typemap(javacode) Sort %{
  public boolean equals(Object object) {
    if(object instanceof $javaclassname) {
      Sort that = ($javaclassname) object;
      return this.isEqual(that);
    }
    return false;
  }
%}

/** Terminator */
%insert("runtime") %{
#define SWIG_JAVA_ATTACH_CURRENT_THREAD_AS_DAEMON
%}

%feature("director") Terminator;

/** TermManager */
%ignore TermManager::mk_rm_sort();
%ignore TermManager::mk_uninterpreted_sort(const std::optional< std::string > &symbol=std::nullopt);

%ignore TermManager::mk_bv_sort(uint64_t size);
%extend TermManager {
  Sort mk_bv_sort(int size) {
    return $self->mk_bv_sort(size);
  }
}
%ignore TermManager::mk_fp_sort(uint64_t exp_size, uint64_t sig_size);
%extend TermManager {
  Sort mk_fp_sort(int exp_size, int sig_size) {
    return $self->mk_fp_sort(exp_size, sig_size);
  }
}

%ignore TermManager::mk_term(Kind, const std::vector<Term> &, const std::vector<uint64_t> &indices = {});
%extend TermManager {
  Term mk_term(Kind kind, const Term &t1) {
    return $self->mk_term(kind, {t1}, {});
  }
  Term mk_term(Kind kind, const Term &t1, int i1) {
    return $self->mk_term(kind, {t1}, {(uint64_t) i1});
  }
  Term mk_term(Kind kind, const Term &t1, int i1, int i2) {
    return $self->mk_term(kind, {t1}, {(uint64_t) i1, (uint64_t) i2});
  }
  Term mk_term(Kind kind, const Term &t1, const Term &t2) {
    return $self->mk_term(kind, {t1, t2}, {});
  }
  Term mk_term(Kind kind, const Term &t1, const Term &t2, int i1) {
    return $self->mk_term(kind, {t1, t2}, {(uint64_t) i1});
  }
  Term mk_term(Kind kind, const Term &t1, const Term &t2, int i1, int i2) {
    return $self->mk_term(kind, {t1, t2}, {(uint64_t) i1, (uint64_t) i2});
  }
  Term mk_term(Kind kind, const Term &t1, const Term &t2, const Term &t3) {
    return $self->mk_term(kind, {t1, t2, t3}, {});
  }
  Term mk_term(Kind kind, const std::vector<Term> &args, const std::vector<int> &indices) {
    std::vector<uint64_t> unsigned_indices;
    for (auto i : indices) {
      unsigned_indices.emplace_back((uint64_t) i);
    }
    return $self->mk_term(kind, args, unsigned_indices);
  }
}
%ignore TermManager::mk_const(const Sort &sort, const std::optional<std::string> &symbol=std::nullopt);
%extend TermManager {
  Term mk_const(const Sort &sort) {
    return $self->mk_const(sort, std::nullopt);
  }
  Term mk_const(const Sort &sort, std::string symbol) {
    return $self->mk_const(sort, symbol);
  }
}
%ignore TermManager::mk_var(const Sort &sort, const std::optional<std::string> &symbol=std::nullopt);
%extend TermManager {
  Term mk_var(const Sort &sort) {
    return $self->mk_var(sort, std::nullopt);
  }
  Term mk_var(const Sort &sort, std::string symbol) {
    return $self->mk_var(sort, symbol);
  }
}

/** Bitwuzla */
%ignore Bitwuzla::Bitwuzla(const Options &options = Options());
%ignore Bitwuzla::is_unsat_assumption (const Term &term);
%ignore Bitwuzla::print_unsat_core(std::ostream &out, const std::string &format = "smt2") const;
%ignore Bitwuzla::print_formula (std::ostream &out, const std::string &format="smt2") const;
%extend Bitwuzla {
  std::string print_formula () {
    std::ostringstream out;
    $self->print_formula(out);
    return out.str();
  }
}
%ignore Bitwuzla::statistics () const;
%ignore Bitwuzla::simplify ();
}

%include "include/bitwuzla/cpp/bitwuzla.h"

namespace bitwuzla::parser {
%ignore Parser::Parser(TermManager &tm, Options &options, const std::string &language, std::ostream *out);
%ignore Parser::Parser(TermManager &tm, Options &options, std::ostream *out);
%ignore Parser::configure_auto_print_model(bool value);
%ignore Parser::parse(const std::string &infile_name, std::istream &input, bool parse_only=false);

%exception {
  try {
    $action
  } catch(Exception& e) {
    jclass exceptionType = jenv->FindClass("java/lang/IllegalArgumentException");
    jenv->ThrowNew(exceptionType, e.what());
    return $null;
  }
}

/** Exception */
%ignore Exception;
}

%include "include/bitwuzla/cpp/parser.h"
