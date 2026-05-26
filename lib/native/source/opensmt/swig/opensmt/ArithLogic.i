// this file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

namespace opensmt {
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

%ignore ArithLogic::ArithLogic (Logic_t type);
%ignore ArithLogic::isBuiltinFunction (SymRef sr) const override;
%ignore ArithLogic::isIntMinusOne (PTRef tr) const;
%ignore ArithLogic::isMinusOne (PTRef tr) const;
%ignore ArithLogic::isRealMinusOne (PTRef tr) const;
%ignore ArithLogic::insertTerm (SymRef sym, vec< PTRef > &&terms) override;
%ignore ArithLogic::mkConst (const char *name) override;
%ignore ArithLogic::mkConst (SRef s, const std::string &name);
%ignore ArithLogic::mkConst (SRef s, Number const &c);
%ignore ArithLogic::mkIntConst (Number const &c);
%extend ArithLogic {
  PTRef mkIntConst(const std::string& c) {
    return $self->mkIntConst(FastRational(c.c_str()));
  }
 }
%ignore ArithLogic::mkRealConst (Number const &c);
%extend ArithLogic {
  PTRef mkRealConst(const std::string& c) {
    return $self->mkRealConst(FastRational(c.c_str()));
  }
 }
%ignore ArithLogic::isBuiltinSort (SRef sr) const override;
%ignore ArithLogic::isBuiltinSortSym (SSymRef ssr) const override;
%ignore ArithLogic::isBuiltinConstant (SymRef sr) const override;
%ignore ArithLogic::isNumConst (SymRef sr) const;
%ignore ArithLogic::isIntConst (SymRef sr) const;
%ignore ArithLogic::isRealConst (SymRef sr) const;
%ignore ArithLogic::isNonNegNumConst (PTRef tr) const;
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
%ignore ArithLogic::isIntNeg (PTRef tr) const;
%ignore ArithLogic::isRealNeg (PTRef tr) const;
%ignore ArithLogic::isIntNeg (SymRef sr) const;
%ignore ArithLogic::isRealNeg (SymRef sr) const;
%ignore ArithLogic::isTimes (SymRef sr) const;
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
%ignore ArithLogic::isIntLeq (PTRef tr) const;
%ignore ArithLogic::isRealLeq (PTRef tr) const;
%ignore ArithLogic::isIntLeq (SymRef sr) const;
%ignore ArithLogic::isRealLeq (SymRef sr) const;
%ignore ArithLogic::isLt (SymRef sr) const;
%ignore ArithLogic::isIntLt (PTRef tr) const;
%ignore ArithLogic::isRealLt (PTRef tr) const;
%ignore ArithLogic::isIntLt (SymRef sr) const;
%ignore ArithLogic::isRealLt (SymRef sr) const;
%ignore ArithLogic::isGeq (SymRef sr) const;
%ignore ArithLogic::isIntGeq (PTRef tr) const;
%ignore ArithLogic::isRealGeq (PTRef tr) const;
%ignore ArithLogic::isIntGeq (SymRef sr) const;
%ignore ArithLogic::isRealGeq (SymRef sr) const;
%ignore ArithLogic::isGt (SymRef sr) const;
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
%ignore ArithLogic::checkSortInt (PTRef tr) const;
%ignore ArithLogic::checkSortReal (PTRef tr) const;
%ignore ArithLogic::checkSortInt (vec< PTRef > const &args) const;
%ignore ArithLogic::checkSortReal (vec< PTRef > const &args) const;
%ignore ArithLogic::getPlusForSort (SRef sort) const;
%ignore ArithLogic::getTimesForSort (SRef sort) const;
%ignore ArithLogic::getMinusForSort (SRef sort) const;
%ignore ArithLogic::getZeroForSort (SRef sort) const;
%ignore ArithLogic::getOneForSort (SRef sort) const;
%ignore ArithLogic::getMinusOneForSort (SRef sort) const;
%ignore ArithLogic::mkMinus (vec< PTRef > &&);
%ignore ArithLogic::mkMinus (vec< PTRef > const &args);
%ignore ArithLogic::mkPlus (vec< PTRef > &&);
%ignore ArithLogic::mkPlus (vec< PTRef > const &args);
%ignore ArithLogic::mkPlus (std::vector< PTRef > const &args);
%ignore ArithLogic::mkTimes (vec< PTRef > &&args);
%ignore ArithLogic::mkTimes (vec< PTRef > const &args);
%ignore ArithLogic::mkTimes (std::vector< PTRef > const &args);
%ignore ArithLogic::mkIntDiv (vec< PTRef > &&args);
%ignore ArithLogic::mkIntDiv (vec< PTRef > const &args);
%ignore ArithLogic::mkRealDiv (vec< PTRef > &&args);
%ignore ArithLogic::mkRealDiv (vec< PTRef > const &args);
%ignore ArithLogic::mkMod (vec< PTRef > &&args);
%ignore ArithLogic::mkLeq (vec< PTRef > const &args);
%ignore ArithLogic::mkGeq (vec< PTRef > const &args);
%ignore ArithLogic::mkLt (vec< PTRef > const &args);
%ignore ArithLogic::mkGt (vec< PTRef > const &args);
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
%ignore ArithLogic::getConstantFromLeq (PTRef) const;
%ignore ArithLogic::getTermFromLeq (PTRef) const;
%ignore ArithLogic::leqToConstantAndTerm (PTRef) const;
%ignore ArithLogic::getNestedBoolRoots (PTRef) const override;
}

%include "include/opensmt/logics/ArithLogic.h"
