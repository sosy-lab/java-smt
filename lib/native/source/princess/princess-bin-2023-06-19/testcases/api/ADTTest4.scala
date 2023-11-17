/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2019 Philipp Ruemmer <ph_r@gmx.net>
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

// Unit tests for the decision procedure for algebraic data-types

//object ADTTest extends App {
  import ap.SimpleAPI
  import ap.terfor.TerForConvenience
  import SimpleAPI.ProverStatus
  import ap.parser._
  import ap.theories.ADT
  import ADT._
  import ap.util.Debug

  Debug enableAllAssertions true

  val colADT =
    new ADT (List("colour", "colour_list"),
             List(("red",   CtorSignature(List(), ADTSort(0))),
                  ("blue",  CtorSignature(List(), ADTSort(0))),
                  ("green", CtorSignature(List(), ADTSort(0))),
                  ("nil",   CtorSignature(List(), ADTSort(1))),
                  ("cons",  CtorSignature(List(("head", ADTSort(0)),
                                               ("tail", ADTSort(1))),
                                          ADTSort(1)))),
             ADT.TermMeasure.Size)

  val Seq(colour, colour_list)                    = colADT.sorts
  val Seq(red, blue, green, nil, cons)            = colADT.constructors
  val Seq(_,   _,    _,     _,   Seq(head, tail)) = colADT.selectors
  val Seq(colour_size, colour_list_size)          = colADT.termSize

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    def expect[A](x : A, expected : A) : A = {
      assert(x == expected, "expected: " + expected + ", got: " + x)
      x
    }

    val c1, c2 = createConstant(colour)
    val x, y, z = createConstant(colour_list)

    import IExpression._

    println("Test 1")
    scope {
      !! (cons(c1, cons(c2, x)) === z)
      !! (head(z) === red())

      println(expect(???, ProverStatus.Sat))
      println(evalToTerm(z))

      scope {
        !! (colour_list_size(z) === 13)

        println(expect(???, ProverStatus.Sat))
        println(evalToTerm(z))
      }

      scope {
        !! (colour_list_size(z) === 14)

        println(expect(???, ProverStatus.Unsat))
      }
    }

    println("Test 2")
    scope {
      !! (cons(c1, cons(c2, nil())) === z)
      !! (head(z) === red())
      !! (c1 === c2)

      println(expect(???, ProverStatus.Sat))

      val model = partialModel
      println(model evalToTerm z)
      println(model eval colADT.hasCtor(z, 3))
      println(model eval colADT.hasCtor(z, 4))
      println(model evalToTerm head(z))
      println(model evalToTerm head(tail(z)))
      println(model evalToTerm head(tail(cons(green(), z))))
      println(model evalToTerm colour_list_size(cons(green(), z)))
    }

  }
//}
