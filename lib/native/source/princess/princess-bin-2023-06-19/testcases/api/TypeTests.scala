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

// Unit tests for types and sorts

import ap.parser._
import ap.SimpleAPI
import ap.util.Debug

//object TypeTests extends App {

  Debug enableAllAssertions true

  val p = SimpleAPI(genTotalityAxioms = true, enableAssert = true)
  import p._
  import IExpression._

  println("Starting")

  val x = createConstant("x")
  val y = createConstant("y")
  val z = createConstant("z", Sort.Nat)
  val a = createConstant("a", 0 until 100)

  scope {
    val f = ex((a, b) => a === x + b)
    println(pp(f))
    !! (f)
    println(???)
  }

  scope {
    val f = Sort.Nat ex (_ === x)
    println(pp(f))
    !! (f)
    println(???)
  }

  scope {
    val f = Sort.Nat all { a => x === a }
    println(pp(f))
    !! (f)
    println(???)
  }

  scope {
    val f = (Sort.Nat ex { a => x === y + a }) <===> (y <= x)
    println(pp(f))
    ?? (f)
    println(???)
  }

  scope {
    val f = ((0 until 10) ex (_ > x))
    val g = ((0 to 9) ex (_ > x))
    println(pp(f))
    println(pp(g))
    println(pp(simplify(f)))
    ?? (f <===> g)
    println(???)
  }

  scope {
    !! (z < -10)
    println(???)
  }

  scope {
    val x1 = createConstant("x1", 0 until 10)
    val x2 = createConstant("x2", 10 until 20)
    scope {
      println(pp(x1 === x2))
      !! (x1 === x2)
      println(???)
    }
    scope {
      ?? (x2 > x1)
      println(???)
    }
  }

  scope {
    val X = createExistentialConstant("X", Sort.Nat)
    ?? (X > 10 & 2*X < 30)
    println(???)
    println(pp(getMinimisedConstraint))
  }

  scope {
    val c = createConstant(10 until 20)
    !! (c**c < 10000)
    println(???)
    println(eval(c))
    !! (c**c > 1000)
    println(???)
  }

  scope {
    val f = createFunction("f", List(Sort.Nat), 0 until 10)
    scope {
      !! (f(z) > 100)
      println(???)
    }
    scope {
      !! (Sort.Nat all { x => trig(f(x+1) > f(x), f(x)) })
//      !! (f(15) === x)
      println(???)
    }
  }

  p.shutDown

  println("Finished")

// }
