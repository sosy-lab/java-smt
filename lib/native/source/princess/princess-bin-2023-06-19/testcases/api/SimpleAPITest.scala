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

object SimpleAPITest extends App {
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
  
  part("Scoping (locally add assertions, declare symbols, etc)")
  
  p.scope {
    p !! (s ==> c <= -100)
    println(p???) // Unsat
  }
  
  println(p???) // Sat again

  part("Shorter notation via importing")

  import p._
    
  scope {
    val x, y, z = createConstant
    
    !! (x >= 0)
    !! (y >= x + 1)
    !! (z >= y * 2)
    println(???) // Sat
    
    !! (z === 20)
    println(???) // Sat

    scope {
      part("Nesting scopes and use of quantifiers")
  
      !! (ex(a => a >= 0 & z + a === 0))
      println(???) // Unsat
    }
    
    part("Declaring functions")

    val f = createFunction("f", 1)
    !! (f(x) === f(z) + 1)
    println(???) // Sat
    println("f(z) - f(x) = " + eval(f(z) - f(x)))       // f(z) - f(x) = -1
    println("(f(x) === f(z)) = " + eval(f(x) === f(z))) // (f(x) === f(z)) = false

    println("Partial model: " + partialModel)
    println("In model: " + "f(z) - f(x) = " + partialModel.eval(f(z) - f(x))) // = Some(-1)
    println("          " + "f(17) = " + partialModel.eval(f(17)))             // = None
    println("          " + "(f(x) >= -5) = " + partialModel.eval(f(x) >= -5)) // = Some(true)
    
    val a, b = createConstant
    !! (f(a) === 0 & f(b) === 1)
    !! (a === b)
    println(???) // Unsat
  }

  part("Generating different models for the same formula")

  scope {
    val p1, p2, p3 = createBooleanVariable
    !! (p1 | !p2 | p3)
    !! (p2 | c <= -100)
    
    def dn[A](value : Option[A]) : String = value match {
      case Some(v) => v.toString
      case None => "-"
    }

    println("  p1  \t  p2  \t  p3")
    println("------------------------")
    while (??? == ProverStatus.Sat) {
      println("  " + dn(evalPartial(p1)) + "\t  "
                   + dn(evalPartial(p2)) + "\t  "
                   + dn(evalPartial(p3)))
      nextModel(false)
    }
  }

  part("Incremental solving")
  
  scope {
    val p1, p2, p3 = createBooleanVariable
    !! (p1 | !p2 | p3)
    !! (p2 | c <= -100)
    
    println("  p1  \t  p2  \t  p3")
    println("------------------------")
    while (??? == ProverStatus.Sat) {
      println("  " + eval(p1) + "\t  "
                   + eval(p2) + "\t  "
                   + eval(p3))
      !! (or(for (p <- List(p1, p2, p3)) yield (p </> eval(p))))
    }
  }

  part("Validity mode")

  scope {
    val x = createConstant
    
    !! (x > 5)
    println(???) // Sat
    println("x = " + eval(x))     // x = 6
    println("2*x = " + eval(2*x)) // 2*x = 12
    
    ?? (x > 0)   // prover switches to "validity" mode, and from now on
                 // answers Valid/Invalid instead of Unsat/Sat
    println(???) // Valid
  }

  part("Theory of simple arrays (deprecated)")

  scope {
    val a, b = createConstant
    
    !! (a === store(store(store(b, 2, 2), 1, 1), 0, 0))
    
    println(???) // Sat
    println("select(a, 1) = " + eval(select(a, 1)))   // select(a, 1) = 1
    println("select(a, 10) = " + eval(select(a, 10))) // select(a, 10) = ?
    
    scope {
      !! (a === store(b, 0, 1))
      println(???) // Unsat
    }
    
    scope {
      ?? (select(a, 2) > select(a, 1))
      println(???) // Valid
    }
    
    scope {
      !! (all(x => (select(a, x) === x + 1)))
      println(???) // Unsat
    }
  }
  
  part("Theory of extensional arrays")

  val IntAr = ExtArray(List(Sort.Integer), Sort.Integer)

  scope {
    val a = createConstant("a", IntAr.sort)
    val b = createConstant("b", IntAr.sort)
    
    import IntAr.{select, store}

    !! (a === store(store(store(b, 2, 2), 1, 1), 0, 0))
    
    println(???) // Sat
    println("select(a, 1) = " + eval(select(a, 1)))   // select(a, 1) = 1
    println("select(a, 10) = " + eval(select(a, 10))) // select(a, 10) = ?
    
    val m = partialModel

    println("In partial model: select(a, 1) = " + m.eval(select(a, 1)))   // select(a, 1) = 1
    println("In partial model: select(a, 10) = " + m.eval(select(a, 10))) // select(a, 10) = ?
    
    scope {
      !! (a === store(b, 0, 1))
      println(???) // Unsat
    }
    
    scope {
      ?? (select(a, 2) > select(a, 1))
      println(???) // Valid
    }
    
    scope {
      !! (all(x => (select(a, x) === x + 1)))
      println(???) // Inconclusive
    }
  }
  
  part("Non-trivial quantifiers")
  
  scope {
    ?? (ex(x => 0 <= x & x < 10 & (2*x === c | x === d)))
    println(???)   // Invalid
    !! (c === 4 & false)
    println(???)   // Valid
  }

  part("Quantifiers, functions, and triggers")

  scope {
    val f = createFunction("f", List(Sort.Integer), Sort.Integer,
                           partial = true)
    !! (all(x => f(x) >= x))   // f(x) will automatically be selected as a trigger

    val a, b = createConstant
    !! (a === 5 & f(a + b) === 3)

    println(???) // Sat
    println("b = " + eval(b))     // b = -2

    scope {
      !!(b > 10)
      println(???) // Unsat
    }

    !! (all(x => trig(f(x) <= x + 3, f(x))))   // specify trigger manually
    println(???) // Sat

    /*
        b = -2
        b = -3
        b = -4
        b = -5
     */
    while (??? == ProverStatus.Sat) {
      println("b = " + eval(b))
      !! (b =/= eval(b))
    }
  }

  part("Boolean functions and triggers")

  scope {
    val r = createBooleanFunction("r", List(Sort.Integer, Sort.Integer),
                                  partial = true)
    val a = createConstant

    // Boolean functions can be used in triggers, in contrast to
    // predicates/relations
    !! (all(x => all(y => trig(r(x, y) ==> r(y, x), r(x, y)))))
    !! (r(1, a))

    scope {
      !! (a === 5)
      println(???) // Sat
      println("Partial model: " + partialModel)
    }

    scope {
      !! (!r(3, 1))
      ?? (a =/= 3)
      println(???) // Valid
    }
  }

  part("Evaluation with Boolean variables")

  scope {
    val p = createConstant("p", Sort.Bool)
    val q = createConstant("q", Sort.Bool)
    val r = createConstant("r", Sort.Bool)

    val f = (p === q) & eqZero(p) & (!eqZero(q) | !eqZero(r))
    println(pp(f))
    !! (f)

    println(???)                 // Sat
    println(partialModel eval f) // Some(true)
  }

  part("Existential constants")

  scope {
    val X, Y = createExistentialConstant
    val f = createFunction("f", 1)

    !! (f(1) === 10)
    !! (f(10) === 100)
    !! (f(100) === 1)

    scope {
      ?? (f(f(f(X))) === X)
      println(???)                      // Valid

      println("X = " + eval(X))         // X = 1
      println("X + Y = " + eval(X + Y)) // X + Y = 1, extend the model to include Y
      println("Y = " + eval(Y))         // Y = 0
    }

    scope {
      ?? (f(f(f(X))) === X & X > 1)
      println(???)                      // Valid

      println("X = " + eval(X))         // X = 10

      println("Model: " + partialModel)
    }
  }

  part("Quantifier elimination")

  scope {
    setMostGeneralConstraints(true)

    val X = createExistentialConstant("X")
    val Y = createExistentialConstant("Y")
    
    scope {
      ?? (ex(x => 5 < x & x < 2*X))

      println(???)                             // Valid
      println("Equivalent qf constraint: " +   // X >= 4
              pp(getConstraint))
    }

    scope {
      val f = createFunction("f", 1)

      !! (f(3) >= 10)
      !! (f(42) === 42)

      ?? (f(X) >= X)
      println(???)                             // Valid
      println("Equivalent qf constraint: " +   // X = 42 | X = 3
              pp(getConstraint))

      !! (f(100) === Y)
      println(???)                             // Valid
      println("Equivalent qf constraint: " +   // X = 42 | X = 3 | (X = 100 & Y >= 100)
              pp(getConstraint))
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  part("Simplification, projection")

  scope {
    val x = createConstant("x")
    val y = createConstant("y")
    println("Project 5 < x & x < 2*y existentially to " + y + ": " +
            pp(projectEx(5 < x & x < 2*y, List(y))))
    println("Project x > y | x < 0 universally to " + x + ": " +
            pp(projectAll(x > y | x < 0, List(x))))
    println("Simplify ex(x => 5 < x & x < 2*y) to: " +
            pp(simplify(ex(x => 5 < x & x < 2*y))))
  }

  scope {
    val x = createConstant("x", Sort.Bool)
    val y = createConstant("y", Sort.Bool)

    println("Project x ==> y universally to " + y + ": " +
            pp(projectAll(eqZero(x) ==> eqZero(y), List(y))))
    println("Project x === True existentially to empty set: " +
            pp(projectEx(x === ADT.BoolADT.True, List())))
  }

  //////////////////////////////////////////////////////////////////////////////

  part("Asynchronous interface")
  
  val okStatus = Set(ProverStatus.Sat, ProverStatus.Running)

  !! (true)
  println(okStatus(p checkSat false))            // non-blocking, Running or Sat
  println(okStatus(p getStatus false))           // non-blocking, Running or Sat
  println(p getStatus true)        // blocking, equivalent to println(???), Sat
  
  part("Asynchronous interface, timeouts")
  
  !! (true)
  println(okStatus(p checkSat false))            // non-blocking, Running or Sat
  println(okStatus(p getStatus false))           // non-blocking, Running or Sat
  println(p getStatus 30)                        // blocking for up to 30ms, Sat
  p getStatus true
  
  part("Asynchronous interface, busy waiting")
  
  !! (true)
  println(okStatus(p checkSat false))            // non-blocking, Running or Sat
  while ((p getStatus false) == ProverStatus.Running) {}
  println(p getStatus false)                     // Sat
  
  part("Stopping computations")
  
  !! (true)
  p checkSat false                // non-blocking, Running
  p getStatus false               // non-blocking, usually still Running
  p.stop                          // blocks until prover has actually stopped, Unknown
  (p getStatus false) match {     // non-blocking, usually Unknown (unless prover
    case ProverStatus.Unknown |   // was already finished when calling "stop")
         ProverStatus.Sat =>
      println("expected result")
    case x =>
      println("oops: " + x)
  }  

  part("Stopping computation after a while")
  
  !! (true)
  (p checkSat false) match {   // non-blocking, Running or Sat
    case ProverStatus.Running |
         ProverStatus.Sat =>
      println("expected result")
    case x =>
      println("oops: " + x)
  }

  {
    println("Wait for 30ms ...")
    val m = System.currentTimeMillis
    while (System.currentTimeMillis < m + 30) {}
  }
  
  println(p.stop)            // blocks until prover has actually stopped, Sat

  //////////////////////////////////////////////////////////////////////////////
  
  reset

  part("Interpolation")
  
  scope {
    setConstructProofs(true)
    val c = createConstant("c")
    val d = createConstant("d")
    val e = createConstant("e")

    setPartitionNumber(0)
    !! (0 <= c)

    setPartitionNumber(1)
    !! (c < d)

    setPartitionNumber(2)
    !! (0 > e & e > d)

    println(???)  // Unsat
    println(getInterpolants(Seq(Set(0), Set(1), Set(2))) map (pp(_)))
    println(getInterpolants(Seq(Set(1), Set(0), Set(2))) map (pp(_)))
  }

  part("Interpolation with functions")

  scope {
    setConstructProofs(true)
    val f = createFunction("f", 1)
    val c = createConstant("c")

    setPartitionNumber(0)
    !! (f(c) === 5)

    setPartitionNumber(1)
    !! (c === 3)

    setPartitionNumber(2)
    !! (f(3) < 0)

    println(???)  // Unsat
    println(getInterpolants(Seq(Set(0), Set(1), Set(2))) map (pp(_)))
    println(getInterpolants(Seq(Set(0, 2), Set(1))) map (pp(_)))
  }

  part("Interpolation with simple arrays (deprecated)")

  scope {
    setConstructProofs(true)
    val a = createConstant("a")
    val b = createConstant("b")

    setPartitionNumber(0)
    !! (store(a, 0, 1) === b)

    setPartitionNumber(1)
    !! (select(b, 0) === 2)

    println(???)  // Unsat
    println(getInterpolants(Seq(Set(0), Set(1))) map (pp(_)))
  }
  
  part("Interpolation with extensional arrays")

  scope {
    setConstructProofs(true)
    val a = createConstant("a", IntAr.sort)
    val b = createConstant("b", IntAr.sort)

    import IntAr.{select, store}

    setPartitionNumber(0)
    !! (store(a, 0, 1) === b)

    setPartitionNumber(1)
    !! (select(b, 0) === 2)

    println(???)  // Unsat
    println(getInterpolants(Seq(Set(0), Set(1))) map (pp(_)))
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  reset

  part("Generating a larger amount of constraints")

  scope {
    val vars = createConstants(101)

    for (i <- 0 until 100)
      !! (vars(i+1) === vars(i) + 1)
    
    println(???)                                        // Sat
    println("" + vars(100) + " = " + eval(vars(100)))   // c100 = 100
    
    scope {
      ?? (vars(0) >= 0 ==> vars(100) >= 0)
      println(???)                                      // Valid
    }
  }
  
  part("Generating a larger amount of constraints (2)")

  scope {
    val vars = (for (i <- 0 to 500) yield createConstant("x" + i)).toArray
  
    for (i <- 0 until 500)
      !! (vars(i+1) === vars(i) + i)
    
    println(???)                                        // Sat
    println("" + vars(500) + " = " + eval(vars(500)))   // x500 = 124750
    
    scope {
      ?? (vars(0) >= 0 ==> vars(500) >= 0)
      println(???)                                      // Valid
    }
  }
  
  p.shutDown
}
