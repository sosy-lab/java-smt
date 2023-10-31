// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

%ignore sstat::sstat();
%ignore sstat::sstat(lbool l);
%ignore sstat::sstat(int v);
%ignore sstat::operator==(sstat s) const;
%ignore sstat::operator!=(sstat s) const;
%extend sstat {
  /* FIXME: This whole class should probably be an enum */
  static sstat True()  { return s_True; }
  static sstat False() { return s_False; }
  static sstat Undef() { return s_Undef; }
  static sstat Error() { return s_Error; }
 }

%ignore toSstat(int);

%typemap(javacode) sstat %{
  public boolean equals(Object object) {
    if(object instanceof $javaclassname) {
      sstat that = ($javaclassname) object;
      return this.getValue() == that.getValue();
    }
    return false;
  }

  public int hashCode() {
    return Long.hashCode(this.getValue());
  }

  public String toString() {
    if (this.equals(sstat.True())) {
      return "true";
    }
    if (this.equals(sstat.False())) {
      return "false";
    }
    if (this.equals(sstat.Undef())) {
      return "undef";
    }
    if (this.equals(sstat.Error())) {
      return "error";
    }
    throw new RuntimeException();
  }
%}

%ignore s_True;
%ignore s_False;
%ignore s_Undef;
%ignore s_Error;

%ignore MainSolver::MainSolver(std::unique_ptr<Theory>, std::unique_ptr<TermMapper>, std::unique_ptr<THandler>, std::unique_ptr<SimpSMTSolver>, Logic&, SMTConfig&, std::string);
%ignore MainSolver::getConfig();
%ignore MainSolver::getSMTSolver();
%ignore MainSolver::getSMTSolver() const;
%ignore MainSolver::getTHandler();
%ignore MainSolver::getLogic();
%ignore MainSolver::getTheory();
%ignore MainSolver::getTheory() const;
%ignore MainSolver::getPartitionManager();
%ignore MainSolver::insertFormula(PTRef, char**);
%ignore MainSolver::initialize();
%ignore MainSolver::simplifyFormulas();
%ignore MainSolver::printFramesAsQuery() const;
%ignore MainSolver::solverEmpty() const;
%ignore MainSolver::writeSolverState_smtlib2(const char*, char**) const;
%ignore MainSolver::getTermValue(PTRef) const;
%ignore MainSolver::createTheory(Logic&, SMTConfig&);

%include "include/opensmt/MainSolver.h"
