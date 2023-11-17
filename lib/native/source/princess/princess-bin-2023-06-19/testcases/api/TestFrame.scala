/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

// Test of the different scoping methods

//package ap

//object TestFrame extends App {
  import ap.SimpleAPI
  import SimpleAPI.ProverStatus
  import ap.parser._
  import IExpression._
  import ap.util.Debug

  Debug enableAllAssertions true

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    def expect[A](x : A, expected : A) : A = {
      assert(x == expected, "expected: " + expected + ", got: " + x)
      x
    }

    scope {
      val x = createConstant("x")
      val y = createConstant("y")

      !! (x > y)
      println(expect(???, ProverStatus.Sat))

      scope {
        !! (x < y)
        println(expect(???, ProverStatus.Unsat))
      }

      scope(resetFormulas = true) {
        !! (x < y)
        println(expect(???, ProverStatus.Sat))
      }

      val f = createFunction("f", List(Sort.Integer), Sort.Integer)
      scope(resetFormulas = true) {
        !! (f(x) < 0)
        !! (all(a => f(a) > a))
        !! (y > 10)
        println(expect(???, ProverStatus.Inconclusive))
        !! (x > y)
        println(expect(???, ProverStatus.Unsat))
      }     

      // check whether asserted formulas can get in the way of
      // quantifier elimination (they shouldn't!)
      !! (x === 42)
      println(pp(simplify(ex(z => (y < z) & (z < x)))))
    }
  }
//}
