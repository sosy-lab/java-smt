/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2014 Philipp Ruemmer <ph_r@gmx.net>
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

import ap._
import ap.parser._

object SimpleAPITest9 extends App {

  ap.util.Debug.enableAllAssertions(true)
  val p = SimpleAPI.spawnWithAssertions

  import IExpression._
  import SimpleAPI.ProverStatus
  import p._

  val x = createConstant("x")
  val y = createConstant("y")
  val z = createConstant("z")

  val t1 = abbrev(x + 2*y)

  scope {
    !! (t1 === 5)
    println(???)   // Sat
    scope {
      ?? (t1 > 0)
      println(???) // Valid
    }
    !! (x < -5)
    !! (y < 0)
    println(???)   // Unsat
  }

  scope {
    val t2 = abbrev(z + 2*x)
    !! (t1 + t2 === 3)
    println(???)   // Sat
  }

  scope {
    var f1 = abbrev(t1 > 0)
    for (_ <- 0 until 100)
      f1 = abbrev(f1 & f1)
    !! (f1)
    println(???)   // Sat
    !! (x < -5)
    !! (y < 0)
    println(???)   // Unsat
  }

  p.shutDown

}
