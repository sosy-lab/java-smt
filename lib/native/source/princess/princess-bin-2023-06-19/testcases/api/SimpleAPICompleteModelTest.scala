/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2022 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.theories.{ADT, ExtArray}
import ap.theories.rationals.Rationals

/**
 * Several test cases that led to assertion failures in the past.
 */
object SimpleAPICompleteModelTest extends App {
  ap.util.Debug.enableAllAssertions(true)
  val p = SimpleAPI.spawnWithAssertions
  
  import IExpression._
  import SimpleAPI.ProverStatus

  def part(str : String) = {
    println
    println("-- " + str)
  }
  
  part("Declaration of symbols")
  
  val c, d = p.createConstant
  val r, s, v = p.createBooleanVariable

  println(p???) // no assertions, Sat
  
  part("Adding some assertions (uses methods from IExpression._)")
  
  p !! (r & (c === d + 15))
  p !! (d >= 100)
  p !! (r ==> s)
  println(p???) // still Sat
  println("Partial model: " + p.partialModel)

  part("Querying the model")
  
  println("r = " + p.eval(r))             // r = true
  println("r & !s = " + p.eval(r & !s))   // r & !s = false
  println("v = " + p.eval(v))             // v = true (arbitrary, value of v
                                          //          is not fixed by assertions)
  
  part("Scoping and extraction of complete models")
  
  p.scope {
    p !! (s ==> c <= -100)
    println(p???) // Unsat
  }
  
  p.scope {
    println(p???) // Sat again
    println("c = " + p.eval(c))

    // Adding a newly created constant to the prover
    val x = p.createConstant("x")
    println(p???)               // Sat again
    p.withCompleteModel { model =>
      println("x = " + model.evalToInt(x))
    }
    p.withCompleteModel { model =>
      println("2*x = " + model.evalToInt(2*x))
    }
  }

  part("Scoping and extraction of complete models (2)")

  p.scope {
    println(p???) // Sat again
    println("c = " + p.eval(c))

    // Adding an independently created constant to the prover
    val x = new ConstantTerm("x")
    p.addConstant(x)
    println(p???)               // Sat again
    p.withCompleteModel { model =>
      println("x = " + model.evalToInt(x))
    }
  }

  part("Scoping and extraction of complete models (3)")

  p.scope {
    println(p???) // Sat again
    println("c = " + p.eval(c))

    // Adding an independently created predicate to the prover
    val u = new Predicate("u", 0)
    p.addRelation(u)
    println(p???)                   // Sat again
    p.withCompleteModel { model =>
      println("u() = " + model.evalToBool(u()))
      println("!u() = " + model.evalToBool(!u()))
    }

    val w = p.createBooleanFunction("w", 1)
    p !! all(x => (x >= 0 ===> w(x)))
    println(p???)                   // Inconclusive, but we can still get a model
    p.withCompleteModel { model =>
      println("w(42) = " + model.evalToBool(w(42)))
      println("w(-10) = " + model.evalToBool(w(-10)))
      println("(w(42) <=> w(-10)) = " + model.evalToBool(w(42) <=> w(-10)))
      println("all(x => (x <= -10 ===> w(x))) = " +
                model.evalToBool(all(x => (x <= -10 ===> w(x)))))
    }
    p.withCompleteModel { model =>
      println("all(x => (x <= -10 ===> w(x))) = " +
                model.evalToBool(all(x => (x <= -10 ===> w(x)))))
      println("(w(42) <=> w(-10)) = " + model.evalToBool(w(42) <=> w(-10)))
      println("w(42) = " + model.evalToBool(w(42)))
      println("w(-10) = " + model.evalToBool(w(-10)))
    }
  }

  part("Scoping and extraction of complete models (4)")

  p.scope {
    println(p???) // Sat again
    println("c = " + p.eval(c))

    // Adding an independently created predicate to the prover
    val u = new Predicate("u", 0)
    p.addRelation(u)
    println(p???)                   // Sat again
    p.withCompleteModel { model =>
      // this order previously caused an exception
      println("!u() = " + model.evalToBool(!u()))
      println("u() = " + model.evalToBool(u()))
    }
  }

  println(p???)               // Sat again

  part("Evaluation with rationals")

  import Rationals._

  val x = p.createConstant("x", dom)
  val y = p.createConstant("y", dom)

  p.scope {
    p !! (gt(x, zero))
    println(p???)                   // Sat
    println("x = " + p.eval(x))
    p.withCompleteModel { model =>
      println("x = " + model.evalToTerm(x))
      println("y = " + model.evalToTerm(y))
      println("x/2 = " + model.evalToTerm(div(x, int2ring(2))))
      println("x = " + model.evalToTerm(x))
    }
  }

}
