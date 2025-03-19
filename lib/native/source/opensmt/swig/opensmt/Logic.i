// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

namespace opensmt {

// Override the exception handler for Logic.parse()
// Any error thrown here should be recast as an IllegalArgumentException
%exception Logic::parseFormula {
  try { $action }
  catch(std::exception& e) {
    jclass exceptionType = jenv->FindClass("java/lang/IllegalArgumentException");
    jenv->ThrowNew(exceptionType, e.what());
    return $null;
  }
  catch(OutOfMemoryException& e) {
    jclass exceptionType = jenv->FindClass("java/lang/OutOfMemoryError");
    jenv->ThrowNew(exceptionType, "");
    return $null;
  }
  catch(...) {
    jclass exceptionType = jenv->FindClass("java/lang/IllegalArgumentException");
    jenv->ThrowNew(exceptionType, "");
    return $null;
  }
}

%ignore Logic::TermMarks;

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
%ignore Logic::getSortRef (SymRef sr) const;
%ignore Logic::hasArrays () const;
%ignore Logic::isArrayStore (SymRef) const;
%ignore Logic::isArraySelect (SymRef) const;
%ignore Logic::mkStore (vec< PTRef > &&);
%extend Logic {
  PTRef mkStore(PTRef array, PTRef index, PTRef value) {
    return $self->mkStore({array, index, value});
  }
 }
%ignore Logic::mkSelect (vec< PTRef > &&);
%extend Logic {
  PTRef mkSelect(PTRef array, PTRef index) {
    return $self->mkSelect({array, index});
  }
 }
%ignore Logic::getUniqueArgSort (SymRef sr) const;
%ignore Logic::getUniqueArgSort (PTRef tr) const;
%ignore Logic::getSym (const PTRef tr) const;
%ignore Logic::getSymName (const PTRef tr) const;
%ignore Logic::symNameToRef (const char *s);
%ignore Logic::hasSym (const char *s) const;
%ignore Logic::commutes (const SymRef s) const;
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
%ignore Logic::mkUniqueAbstractValue (SRef);
%ignore Logic::mkConst (const char *);
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
%ignore Logic::peekSortSymbol (SortSymbol const &, SSymRef &) const;
%ignore Logic::declareSortSymbol (SortSymbol symbol);
%ignore Logic::getSort (SSymRef, vec< SRef > &&args);
%ignore Logic::dumpHeaderToFile (std::ostream &dump_out) const;
%ignore Logic::dumpFormulaToFile (std::ostream &dump_out, PTRef formula, bool negate=false, bool toassert=true) const;
%ignore Logic::dumpChecksatToFile (std::ostream &dump_out) const;
%ignore Logic::dumpWithLets (std::ostream &out, PTRef formula) const;
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
%extend Logic {
  bool isSortBool (SRef sort) {
    SRef sortBool = $self->getSort_bool();
    return sort == sortBool;
  }
 }
%ignore Logic::isEquality (SymRef tr) const;
%ignore Logic::isUFEquality (PTRef tr) const;
%ignore Logic::isTheoryEquality (PTRef tr) const;
%ignore Logic::isDisequality (SymRef tr) const;
%ignore Logic::isIte (SymRef tr) const;
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
%ignore Logic::yieldsSortUninterpreted (PTRef tr) const;
%ignore Logic::isUFSort (const SRef sr) const;
%ignore Logic::appearsInUF (PTRef tr) const;
%ignore Logic::setAppearsInUF (PTRef tr);
%ignore Logic::getNestedBoolRoots (PTRef tr) const;
%ignore Logic::isVar (SymRef sr) const;
%ignore Logic::isVarOrIte (SymRef sr) const;
%ignore Logic::isVarOrIte (PTRef tr) const;
%ignore Logic::isAtom (PTRef tr) const;
%ignore Logic::isBoolAtom (PTRef tr) const;
%ignore Logic::isInterpreted (SymRef sr) const;
%ignore Logic::isUP (PTRef) const;
%ignore Logic::isUF (SymRef) const;
%ignore Logic::isIF (PTRef) const;
%ignore Logic::isIF (SymRef) const;
%ignore Logic::isAnd (SymRef sr) const;
%ignore Logic::isOr (SymRef sr) const;
%ignore Logic::isNot (SymRef sr) const;
%ignore Logic::isXor (SymRef sr) const;
%ignore Logic::isImplies (SymRef sr) const;
%ignore Logic::isTrue (SymRef sr) const;
%ignore Logic::isFalse (SymRef sr) const;
%ignore Logic::isIff (SymRef sr) const;
%ignore Logic::hasSortBool (SymRef sr) const;
%ignore Logic::hasSortBool (PTRef tr) const;
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
%ignore Logic::printTerm_ (PTRef tr, bool l, bool s) const;
%ignore Logic::printTerm (PTRef tr) const;
%ignore Logic::printTerm (PTRef tr, bool l, bool s) const;
%ignore Logic::printSym (SymRef sr) const;
%ignore Logic::getSortSize(SRef s) const;
%ignore Logic::termSort (vec< PTRef > &v) const;
%ignore Logic::purify (PTRef r, PTRef &p, lbool &sgn) const;
%ignore Logic::collectStats (PTRef, int &n_of_conn, int &n_of_eq, int &n_of_uf, int &n_of_if);
%ignore Logic::typeCheck (SymRef sym, vec< PTRef > const &args, std::string &why) const;
%ignore Logic::verbose () const;
}

%include "include/opensmt/logics/Logic.h"
