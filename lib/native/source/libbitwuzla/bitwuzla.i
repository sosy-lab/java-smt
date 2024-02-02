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

#include <gmp.h>

#include <string>
#include <sstream>

#include <cassert>

%}

%include <stdint.i>
%include <std_string.i>

%include <std_vector.i>
%template(Vector_Int)
  std::vector<int>;
%template(Vector_String)
  std::vector<std::string>;
%template(Vector_Term)
  std::vector<bitwuzla::Term>;
%template(Vector_Sort)
  std::vector<bitwuzla::Sort>;

%include <std_unordered_map.i>
%template(Map_TermTerm)
  std::unordered_map<bitwuzla::Term, bitwuzla::Term>;

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
%ignore Exception::Exception (const std::stringstream &stream);

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
    assert($self->is_value() && $self->sort().is_bv());
    return $self->value<std::string>(10);
  }

  std::string to_fp () {
    assert($self->is_value() && $self->sort().is_fp());

    // Get Bitwuzla representation of the term value
    auto [sign, exponent, mantissa] =
      $self->value<std::tuple<std::string, std::string, std::string>> ();

    bool isSignZero = sign == "0";
    bool isExponentZero = exponent.find_first_not_of("0") == std::string::npos;
    bool isExponentOnes = exponent.find_first_not_of("1") == std::string::npos;
    bool isMantissaZero = mantissa.find_first_not_of("0") == std::string::npos;

    // Handle special values
    if (isExponentZero && isMantissaZero) {
      return isSignZero ? "0.0" : "-0.0";
    }
    if (isExponentOnes && isMantissaZero) {
      return isSignZero ? "Infinity" : "-Infinity";
    }
    if (isExponentOnes && !isMantissaZero) {
      return "NaN";
    }

    // Calculate value of the exponent
    mpz_t expMpz;
    mpz_init_set_str(expMpz, exponent.c_str(), 2);
    int32_t expVal = mpz_get_si(expMpz);
    int32_t bias = -1 + (1 << -1 + exponent.length());
    mpz_clear(expMpz);

    // Rewrite Bitwuzla representation in a format GMP can understand
    std::string significant = (expVal == 0 ? "" : "1") + mantissa;
    std::string formated =
      significant + "@" + std::to_string(expVal - bias - ((int32_t) significant.length() - 1));

    // Convert result to base10 floating point representation
    mpf_t floatMpf;
    mpf_init_set_str(floatMpf, formated.c_str(), -2);

    mp_exp_t exp10;
    char* sig10 = mpf_get_str(nullptr, &exp10, 10, 0, floatMpf);
    std::string result =  "0." + std::string(sig10) + "e" + std::to_string(exp10);
    delete[] sig10;
    mpf_clear(floatMpf);

    return (sign == "1") ? ("-" + result) : result;
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

// Add static methods for term creation
%ignore mk_true();
%extend Bitwuzla {
  static Term mk_true() {
    return bitwuzla::mk_true();
  }
}
%ignore mk_false();
%extend Bitwuzla {
  static Term mk_false() {
    return bitwuzla::mk_false();
  }
}
%ignore mk_bv_zero(const Sort &);
%extend Bitwuzla {
  static Term mk_bv_zero(const Sort &sort) {
    return bitwuzla::mk_bv_zero(sort);
  }
}
%ignore mk_bv_one(const Sort &);
%extend Bitwuzla {
  static Term mk_bv_one(const Sort &sort) {
    return bitwuzla::mk_bv_one(sort);
  }
}
%ignore mk_bv_ones(const Sort &);
%extend Bitwuzla {
  static Term mk_bv_ones(const Sort &sort) {
    return bitwuzla::mk_bv_ones(sort);
  }
}
%ignore mk_bv_min_signed(const Sort &);
%extend Bitwuzla {
  static Term mk_bv_min_signed(const Sort &sort) {
    return bitwuzla::mk_bv_min_signed(sort);
  }
}
%ignore mk_bv_max_signed(const Sort &);
%extend Bitwuzla {
    static Term mk_bv_max_signed(const Sort &sort) {
    return bitwuzla::mk_bv_max_signed(sort);
  }
}
%ignore mk_bv_value(const Sort &, const std::string &, uint8_t = 2);
%extend Bitwuzla {
    static Term mk_bv_value(const Sort &sort, const std::string &value, int base = 2) {
      return bitwuzla::mk_bv_value(sort, value, (int8_t) base);
  }
}
%ignore mk_bv_value_uint64(const Sort &, uint64_t);
%extend Bitwuzla {
  static Term mk_bv_value_unsigned(const Sort &sort, int value) {
    return bitwuzla::mk_bv_value_uint64(sort, value);
  }
}
%ignore mk_bv_value_int64(const Sort &, int64_t);
%extend Bitwuzla {
  static Term mk_bv_value_signed(const Sort &sort, int value) {
    return bitwuzla::mk_bv_value_int64(sort, value);
  }
}
%ignore mk_fp_pos_zero(const Sort &);
%extend Bitwuzla {
  static Term mk_fp_pos_zero(const Sort &sort) {
    return bitwuzla::mk_fp_pos_zero(sort);
  }
}
%ignore mk_fp_neg_zero(const Sort &);
%extend Bitwuzla {
  static Term mk_fp_neg_zero(const Sort &sort) {
    return bitwuzla::mk_fp_neg_zero(sort);
  }
}
%ignore mk_fp_pos_inf(const Sort &);
%extend Bitwuzla {
  static Term mk_fp_pos_inf(const Sort &sort) {
    return bitwuzla::mk_fp_pos_inf(sort);
  }
}
%ignore mk_fp_neg_inf(const Sort &);
%extend Bitwuzla {
  static Term mk_fp_neg_inf(const Sort &sort) {
    return bitwuzla::mk_fp_neg_inf(sort);
  }
}
%ignore mk_fp_nan(const Sort &);
%extend Bitwuzla {
  static Term mk_fp_nan(const Sort &sort) {
    return bitwuzla::mk_fp_nan(sort);
  }
}
%ignore mk_fp_value(const Term &, const Term &, const Term &);
%extend Bitwuzla {
  static Term mk_fp_value(
      const Term &bv_sign, const Term &bv_exponent, const Term &bv_significand) {
    return bitwuzla::mk_fp_value(bv_sign, bv_exponent, bv_significand);
  }
}
%ignore mk_fp_value(const Sort &, const Term &, const std::string &);
%extend Bitwuzla {
  static Term mk_fp_value(const Sort &sort, const Term &rm, const std::string &repr) {
    // Handle special values
    if (repr == "Infinity") {
      return mk_fp_pos_inf(sort);
    }
    if (repr == "-Infinity") {
      return mk_fp_neg_inf(sort);
    }
    if (repr == "NaN") {
      return mk_fp_nan(sort);
    }

    // Parse float value with GMP
    mpf_t floatVal;
    std::string prev_loc = std::setlocale(LC_ALL, nullptr);
    std::setlocale(LC_ALL, "en_US.UTF-8");
    int error = mpf_init_set_str(floatVal, repr.c_str(), 10);
    std::setlocale(LC_ALL, prev_loc.c_str());
    if (error != 0) {
      throw bitwuzla::Exception(
        "String \"" + repr + "\" can't be parsed as a floating point number.");
    }

    // Convert to decimal format for Bitwuzla
    mp_exp_t exponent;
    char* mantissa = mpf_get_str(nullptr, &exponent, 10, 0, floatVal);
    std::string input = std::string(mantissa);
    mpf_clear(floatVal);
    bool isZeroes = input.find_first_not_of("0") == std::string::npos;
    if (isZeroes) {
      // GMP drops the sign for -0.0, so we have handle this as a special case
      if (repr[0] == '-') {
        return mk_fp_neg_zero(sort);
      } else {
        return mk_fp_pos_zero(sort);
      }
    }

    std::ostringstream output;
    if (input[0] == '-') {
      output << "-";
      input.erase(0, 1);
    }
    if (exponent <= 0) {
      output << "0.";
      output << std::string(-exponent, '0');
      output << input;
    } else {
      output << input.substr(0, exponent);
      if (exponent > input.length()) {
        output << std::string(exponent - input.length(), '0');
      }
      if (exponent < input.length()) {
        output << '.' << input.substr(exponent);
      }
    }
    delete[] mantissa;

    // Create the term
    return bitwuzla::mk_fp_value(sort, rm, output.str());
  }
}
%ignore mk_fp_value(const Sort &,
                    const Term &,
                    const std::string &,
                    const std::string &);
%extend Bitwuzla {
  static Term mk_fp_value(
      const Sort &sort, const Term &rm, const std::string &num, const std::string &den) {
    return bitwuzla::mk_fp_value(sort, rm, num, den);
  }
}
%ignore mk_rm_value(RoundingMode);
%extend Bitwuzla {
  static Term mk_rm_value(RoundingMode rm) {
    return bitwuzla::mk_rm_value(rm);
  }
}
%ignore mk_const_array(const Sort &, const Term &);
%extend Bitwuzla {
  static Term mk_const_array(const Sort &sort, const Term &term) {
    return bitwuzla::mk_const_array(sort, term);
  }
}
%ignore mk_term(Kind, const std::vector<Term> &, const std::vector<uint64_t> &indices = {});
%extend Bitwuzla {
  static Term mk_term(Kind kind, const Term &t1) {
    return bitwuzla::mk_term(kind, {t1}, {});
  }
  static Term mk_term(Kind kind, const Term &t1, int i1) {
    return bitwuzla::mk_term(kind, {t1}, {(uint64_t) i1});
  }
  static Term mk_term(Kind kind, const Term &t1, int i1, int i2) {
    return bitwuzla::mk_term(kind, {t1}, {(uint64_t) i1, (uint64_t) i2});
  }
  static Term mk_term(Kind kind, const Term &t1, const Term &t2) {
    return bitwuzla::mk_term(kind, {t1, t2}, {});
  }
  static Term mk_term(Kind kind, const Term &t1, const Term &t2, int i1) {
    return bitwuzla::mk_term(kind, {t1, t2}, {(uint64_t) i1});
  }
  static Term mk_term(Kind kind, const Term &t1, const Term &t2, int i1, int i2) {
    return bitwuzla::mk_term(kind, {t1, t2}, {(uint64_t) i1, (uint64_t) i2});
  }
  static Term mk_term(Kind kind, const Term &t1, const Term &t2, const Term &t3) {
    return bitwuzla::mk_term(kind, {t1, t2, t3}, {});
  }
  static Term mk_term(Kind kind, const std::vector<Term> &args) {
    return bitwuzla::mk_term(kind, args, {});
  }
  static Term mk_term(Kind kind, const std::vector<Term> &args, const std::vector<int> &indices) {
    std::vector<uint64_t> unsigned_indices;
    for (auto i : indices) {
      unsigned_indices.emplace_back((uint64_t) i);
    }
    return bitwuzla::mk_term(kind, args, unsigned_indices);
  }
}
%ignore mk_const(const Sort &, std::optional<const std::string> = std::nullopt);
%extend Bitwuzla {
  static Term mk_const(const Sort &sort) {
    return bitwuzla::mk_const(sort, std::nullopt);
  }
  static Term mk_const(const Sort &sort, std::string symbol) {
    return bitwuzla::mk_const(sort, symbol);
  }
}
%ignore mk_var(const Sort &, std::optional<const std::string> = std::nullopt);
%extend Bitwuzla {
  static Term mk_var(const Sort &sort) {
    return bitwuzla::mk_var(sort, std::nullopt);
  }
  static Term mk_var(const Sort &sort, std::string symbol) {
    return bitwuzla::mk_var(sort, symbol);
  }
}

// Substitution: This will change the term itself!
%ignore substitute_terms (std::vector<Term> &, const std::unordered_map<Term,Term> &);
%ignore substitute_term (const Term &, const std::unordered_map<Term, Term> &);
%extend Term {
  Term substitute(const std::unordered_map<Term, Term> &map) {
    return bitwuzla::substitute_term(*$self, map);
  }
}

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

// Add static methods for sort creation
%ignore mk_array_sort(const Sort &, const Sort &);
%extend Bitwuzla {
   static Sort mk_array_sort(const Sort &index, const Sort &element) {
     return bitwuzla::mk_array_sort(index, element);
  }
}
%ignore mk_bool_sort();
%extend Bitwuzla {
   static Sort mk_bool_sort() {
     return bitwuzla::mk_bool_sort();
  }
 }
%ignore mk_bv_sort(uint64_t);
%extend Bitwuzla {
  static Sort mk_bv_sort(int size) {
    return bitwuzla::mk_bv_sort(size);
  }
}
%ignore mk_fp_sort(uint64_t, uint64_t);
%extend Bitwuzla {
  static Sort mk_fp_sort(int exp_size, int sig_size) {
    return bitwuzla::mk_fp_sort(exp_size, sig_size);
  }
}
%ignore mk_fun_sort(const std::vector<Sort> &, const Sort &);
%extend Bitwuzla {
  static Sort mk_fun_sort(const std::vector<Sort> &domain, const Sort &codomain) {
    return bitwuzla::mk_fun_sort(domain, codomain);
  }
}

%ignore mk_uninterpreted_sort(std::optional<const std::string> = std::nullopt);
%ignore mk_rm_sort();

/** Terminator */
%insert("runtime") %{
#define SWIG_JAVA_ATTACH_CURRENT_THREAD_AS_DAEMON
%}

%feature("director") Terminator;

/** Bitwuzla */
%ignore Bitwuzla::is_unsat_assumption (const Term &term);
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
%ignore Parser::Parser(
  Options &options,
  const std::string &infile_name,
  const std::string &language,
  std::ostream *out = &std::cout);

%ignore Parser::Parser(
  Options &options,
  const std::string &infile_name,
  FILE *infile,
  const std::string &language = "smt2",
  std::ostream *out = &std::cout);
}

%include "include/bitwuzla/cpp/parser.h"