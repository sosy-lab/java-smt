/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2018  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

/*********************                                                        */
/*! \file SimpleVC.java
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the Java interface
 **
 ** A simple demonstration of the Java interface.
 **
 ** To run the resulting class file, you need to do something like the
 ** following:
 **
 **   java \
 **     -classpath path/to/CVC4.jar \
 **     -Djava.library.path=/dir/containing/java/CVC4.so \
 **     SimpleVC
 **
 ** For example, if you are building CVC4 without specifying your own
 ** build directory, the build process puts everything in builds/, and
 ** you can run this example (after building it with "make") like this:
 **
 **   java \
 **     -classpath builds/examples:builds/src/bindings/CVC4.jar \
 **     -Djava.library.path=builds/src/bindings/java/.libs \
 **     SimpleVC
 **/

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.SExpr;
import edu.nyu.acsys.CVC4.SmtEngine;
import edu.nyu.acsys.CVC4.Type;
import org.sosy_lab.common.NativeLibraries;

public class SimpleVC {
  public static void main(String[] args) {
    // System.loadLibrary("cvc4jni");
    NativeLibraries.loadLibrary("cvc4jni");
    // System.loadLibrary("cvc4jni-sl-prerelease");
    ExprManager em = new ExprManager();
    SmtEngine smt = new SmtEngine(em);


    smt.setOption("incremental", new SExpr(false));
    smt.setLogic("QF_ALL_SUPPORTED");
    // UNSAT
    // x -> a AND x -> b AND a != b

    // x -> a * x -> b AND a != b

    Type integer = em.booleanType();

    Expr x = em.mkVar("x", integer);
    Expr b = em.mkVar("b", integer);
    Expr a = em.mkVar("a", integer);

    Expr val_1 = em.mkConst(true);
    Expr val_2 = em.mkConst(false);

    Expr x_eq_1 = em.mkExpr(Kind.EQUAL, x, val_1); // x = 1


    Expr emp = em.mkExpr(Kind.SEP_EMP, a, b);
    Expr one_pt_2 = em.mkExpr(Kind.SEP_PTO, x, val_2); // 1 -> 2


    Expr formula = em.mkExpr(Kind.SEP_STAR, emp, one_pt_2); // emp * (1->2)
    Expr formula1 = em.mkExpr(Kind.SEP_STAR, x_eq_1, one_pt_2); // x=1 /\ emp * (1->2)

    System.out.println("Checking validity of formula:\n" + formula1.toString() + " with CVC4.");
    System.out.println("Result from CVC4 is: " + smt.query(formula1));

  }
}
