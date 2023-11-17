/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2020 Philipp Ruemmer <ph_r@gmx.net>
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

// package ap.theories.rationals

import ap.parser._
import ap.SimpleAPI
import ap.theories.rationals.Rationals

object TestRat extends App {

  def part(str : String) = {
    println
    println("-- " + str)
  }

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._
    import Rationals._
    import IExpression._

    println(zero)
    println(one)

    val x = createConstant("x", dom)
    val y = createConstant("y", dom)

    scope {
      part("Test 1")
      println(mul(frac(1, 3), frac(1, 4)))

      !! (x === mul(frac(1, 3), frac(1, 4)))
      println(???)
      println(partialModel)
    }

    scope {
      part("Test 2")
      !! (plus(frac(1, 10), x) === plus(y, int2ring(10)))
      println(???)
      println(partialModel)
    }

    scope {
      part("Test 3")
      !! (times(5, x) === int2ring(3))
      println(???)
      println(partialModel)

      !! (mul(x, y) === one)
      println(???)
      println(partialModel)
    }

    scope {
      part("Test 4")
      !! (times(5, x) === times(7, y))
      !! (x =/= zero)
      ?? (x =/= y)
      println(???)
    }

    scope {
      part("Test 5")
      !! (times(5, x) === plus(times(7, y), int2ring(3)))
      !! (x =/= zero)
      ?? (x =/= y)
      println(???)
      println(partialModel)
    }

    scope {
      part("Test 6")
      !! (mul(x, x) === frac(16, 9))
      println(???)
      println(partialModel)
      println(evalToTerm(x))
    }

    scope {
      part("Test 7")
      !! (y =/= zero & y =/= one)
      !! (div(x, y) === int2ring(10))
      println(???)
      println(partialModel)
    }

    scope {
      part("Test 8")
      !! (lt(zero, y) & lt(y, one))
      !! (div(x, y) === int2ring(10))
      println(???)
      println(partialModel)
    }

    scope {
      part("Test 9")
      !! (y =/= zero)
      !! (div(x, y) === int2ring(11))
      !! (lt(x, zero))
      println(???)
      println(partialModel)
    }
  }

}
