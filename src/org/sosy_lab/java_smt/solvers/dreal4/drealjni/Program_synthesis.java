/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
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

package org.sosy_lab.java_smt.solvers.dreal4.drealjni;

public class Program_synthesis {
    static {
        try {
            System.loadLibrary("dreal4");
        } catch(UnsatisfiedLinkError e) {
            System.err.println("Native code library failed to load.\n" + e);
            System.exit(1);
        }
    }

    public static void main(String[] args) {
        Variable var_x = new Variable("x");
        Variable var_a = new Variable("a");
        Variable var_b = new Variable("b");
        Variable var_c = new Variable("c");

        Expression x = new Expression(var_x);
        Expression a = new Expression(var_a);
        Expression b = new Expression(var_b);
        Expression c = new Expression(var_c);
        Expression nt = new Expression(-1000.0);
        Expression t = new Expression(1000.0);
        Expression nh = new Expression(-100.0);
        Expression h = new Expression(100.0);

        Formula sndimply = new Formula(dreal.imply(dreal.GraterEqual(x, c), dreal.Equal(dreal.abs(x), dreal.Multiply(a, x))));
        Formula thrdimply = new Formula(dreal.imply(dreal.Less(x, c), dreal.Equal(dreal.abs(x), dreal.Multiply(b, x))));

        Formula nested = new Formula(dreal.imply(dreal.And(dreal.LessEqual(nt, x), dreal.LessEqual(x, t)), dreal.And(sndimply, thrdimply)));

        Formula quantified = new Formula(dreal.forall(new Variables(new Variable[] {var_x}), nested));

        Box box = new Box();

        Config config = new Config();
        config.mutable_precision(0.001);
        config.mutable_use_polytope_in_forall(true);
        config.mutable_use_local_optimization(true);

        Formula f1 = new Formula(dreal.And(dreal.LessEqual(nh, a), dreal.LessEqual(a, h)));
        Formula f2 = new Formula(dreal.And(dreal.LessEqual(nh, b), dreal.LessEqual(b, h)));
        Formula f3 = new Formula(dreal.And(dreal.LessEqual(nh, c), dreal.LessEqual(c, h)));

        Formula f1f2 = new Formula(dreal.And(f1, f2));
        Formula f3quantified = new Formula(dreal.And(f3, quantified));

        Formula check = new Formula(dreal.And(f1f2, f3quantified));

        boolean result = dreal.CheckSatisfiability(check, config, box);

        if (result) {
            System.out.println("Formula is sat.");
        } else {
            System.out.println("Formula is unsat");
        }

    }
}