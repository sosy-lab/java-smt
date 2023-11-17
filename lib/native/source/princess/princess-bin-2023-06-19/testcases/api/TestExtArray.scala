/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2021 Philipp Ruemmer <ph_r@gmx.net>
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

//package ap.theories

import ap.parser._
import ap.SimpleAPI
import ap.theories.ExtArray

object TestExtArray extends App {

  def part(str : String) = {
    println
    println("-- " + str)
  }

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._
    import IExpression._

    val IntArray = ExtArray(List(Sort.Integer), Sort.Integer)
    import IntArray.{select, store, const}

    val x   = createConstant("x")
    val y   = createConstant("y")
    val ar  = createConstant("ar", IntArray.sort)
    val ar2 = createConstant("ar2", IntArray.sort)

    scope {
      part("Test 1")
      println("Some term: " + store(ar, x, 42))

      !! (ar === store(const(0), 1, 1))
      println(???)

      !! (select(ar, 1) > 1)
      println(???)
    }

    scope {
      part("Test 2")

      !! (ar === store(ar2, 1, 1))
      println(???)
      println("ar = " + evalToTerm(ar))
      println("ar2 = " + evalToTerm(ar2))

      val m = partialModel
      println("m.evalToTerm(ar): " + m.evalToTerm(ar))
      println("m.evalToTerm(select(ar, 0)): " + m.evalToTerm(select(ar, 0)))
      println("m.evalToTerm(select(store(const(0), 1, 2), 1)): " +
                m.evalToTerm(select(store(const(0), 1, 2), 1)))
      println("m.evalToTerm(select(store(const(0), 1, 2), 2)): " + 
                m.evalToTerm(select(store(const(0), 1, 2), 2)))
    }
  }

}
