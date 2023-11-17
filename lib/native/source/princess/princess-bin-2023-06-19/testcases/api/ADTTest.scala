/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2016-2017 Philipp Ruemmer <ph_r@gmx.net>
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

  import ap.SimpleAPI
  import ap.terfor.TerForConvenience
  import SimpleAPI.ProverStatus
  import ap.parser._
  import ap.theories.ADT
  import ap.types.Sort
  import ADT._
  import ap.util.Debug

  Debug enableAllAssertions true

  val listADT =
    new ADT (List("list"),
             List(("nil",  CtorSignature(List(), ADTSort(0))),
                  ("cons", CtorSignature(List(("head", OtherSort(Sort.Integer)),
                                              ("tail", ADTSort(0))),
                  ADTSort(0)))))

  val Seq(nil, cons) = listADT.constructors
  val Seq(_, Seq(head, tail)) = listADT.selectors

  println(listADT.witnesses)

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    def expect[A](x : A, expected : A) : A = {
      assert(x == expected, "expected: " + expected + ", got: " + x)
      x
    }

    val x, y, z, a, b = createConstant

    {
    import IExpression._
    scope {
      !! (cons(x, cons(y, nil())) === z)
      !! (head(z) === 42)

      println(expect(???, ProverStatus.Sat))
      println(partialModel)
    }

    scope {
      !! (cons(x, y) === nil())
      println(expect(???, ProverStatus.Unsat))
    }

    scope {
      !! (listADT.hasCtor(x, 1))
      !! (x === nil())
      println(expect(???, ProverStatus.Unsat))
    }

    scope {
      !! (listADT.hasCtor(x, 1))
      ?? (x === cons(head(x), tail(x)))
      println(expect(???, ProverStatus.Valid))
    }

    scope {
      !! (cons(x, y) === cons(a, b))
      ?? (y === b)
      println(expect(???, ProverStatus.Valid))
    }

    scope {
      !! (cons(x, cons(y, z)) === z)
      println(expect(???, ProverStatus.Unsat))
    }

    scope {
      ?? (listADT.hasCtor(x, 0) | listADT.hasCtor(x, 1))
      println(expect(???, ProverStatus.Valid))
    }

    scope {
      !! (x === cons(y, z) | x === cons(a, b))
      ?? (x =/= nil())
      println(expect(???, ProverStatus.Valid))
    }

    scope {
      !! (x =/= nil())
      !! (x =/= cons(head(x), tail(x)))
      println(expect(???, ProverStatus.Unsat))
    }
    }

    scope {
      addTheory(listADT)
      import TerForConvenience._
      implicit val _ = order
      val IConstant(xc) = x
      val IConstant(yc) = y
      val IConstant(zc) = z
      val IConstant(ac) = a
      addAssertion(listADT.constructorPreds(1)(List(l(yc), l(zc), l(xc))) |
                   listADT.constructorPreds(1)(List(l(ac), l(zc), l(xc))))
      scope {
        ?? (listADT.hasCtor(x, 1))
        println(expect(???, ProverStatus.Valid))
      }
      scope {
        ?? (listADT.hasCtor(x, 0))
        println(expect(???, ProverStatus.Invalid))
      }
    }
  }
