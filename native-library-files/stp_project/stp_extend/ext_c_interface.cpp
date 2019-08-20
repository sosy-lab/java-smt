#include "stp/c_interface.h"

#include <cassert>
#include <cstdio>
#include <cstdlib>

#include "stp/Interface/fdstream.h"
#include "stp/Parser/parser.h"
#include "stp/Printer/printers.h"
#include "stp/cpp_interface.h"
#include "stp/Util/GitSHA1.h"
// FIXME: External library
#include "extlib-abc/cnf_short.h"

using std::cout;
using std::ostream;
using std::stringstream;
using std::string;
using std::fdostream;
using std::endl;


// Add a new formula (assertion or query) in the current context.
/*! The formula must have Boolean type. */
void addAssertFormula(VC vc, Expr e)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* a = (stp::ASTNode*)e;
  
  stp::Cpp_interface cpp_inter(*b, b->defaultNodeFactory);
  cpp_inter.AddAssert(*a);

  /*
  if (!stp::is_Form_kind(a->GetKind()))
    stp::FatalError("Trying to assert a NON formula: ", *a);

  assert(BVTypeCheck(*a));
  b->AddAssert(*a);
  */
}

void push(VC vc)
{

  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  stp_i->ClearAllTables();
  b->Push();
  
}

void pop(VC vc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  b->Pop();
}

int checkSAT_old(VC vc)
{
  // return vc_query_with_timeout(vc, vc_falseExpr(vc), -1, -1);
  return vc_query_with_timeout(vc, vc_trueExpr(vc), -1, -1);  
}


int checkSAT(VC vc, Expr e)
{
  // stp::STP* stp_i = (stp::STP*)vc;
  // stp::STPMgr* b = stp_i->bm;

  // stp::Cpp_interface cpp_inter(*b, b->defaultNodeFactory);
  
  // const stp::ASTVec asserts = cpp_inter.GetAsserts();
  // cpp_inter.checkSat(asserts);

  return 2; //ERROR

}

void getSTPenv(VC vc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  stp::Cpp_interface cpp_inter(*b, b->defaultNodeFactory);
  
  // const stp::ASTVec asserts = cpp_inter.GetAsserts();
  // cpp_inter.checkSat(asserts);

}

// extern "C" 
// {
  StpEnv * createStpEnv(VC vc)
  {
    stp::STP* stp_i = (stp::STP*)vc;
    stp::STPMgr* b = stp_i->bm;
    return reinterpret_cast<StpEnv*>(new stp::Cpp_interface(*b, b->defaultNodeFactory));
  }

  void destroyStpEnv(StpEnv * env)
  {
    delete reinterpret_cast<stp::Cpp_interface*>(env);
  }

  int getCacheSize(StpEnv * env)
  {
    return reinterpret_cast<stp::Cpp_interface*>(env)->getCacheSize();
  }

  int getSymbolsSize(StpEnv * env)
  {
    return reinterpret_cast<stp::Cpp_interface*>(env)->getSymbolsSize();
  }

  void ext_push(StpEnv * env)
  {
    reinterpret_cast<stp::Cpp_interface*>(env)->push();
  }

  void ext_pop(StpEnv * env)
  {
    reinterpret_cast<stp::Cpp_interface*>(env)->pop();
  }

  void ext_addFormula(StpEnv * env, Expr formula)
  {
    stp::ASTNode* assertn = (stp::ASTNode*)formula;

    // TODO: handle error properly; Are these checks even needed !!!
    // if (!stp::is_Form_kind(assertn->GetKind()))
    // stp::FatalError("Trying to assert a NON formula: ", *assertn);

    // assert(stp::BVTypeCheck(*assertn));
    
    reinterpret_cast<stp::Cpp_interface*>(env)->AddAssert(*assertn);
  }

  void ext_checkSat(StpEnv * env)
  {
    auto ptr = reinterpret_cast<stp::Cpp_interface*>(env);
    auto assertions = ptr->getAssertVector();
    cout<<"***Number of current assertion is : "<< assertions.size()<<"\n";
    ptr->checkSat(assertions);
  }


// }