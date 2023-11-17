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

// Unit tests for the decision procedure for algebraic data-types,
// testing interpolation

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

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    val x = createConstant("x")
    val y = createConstant("y")
    val a = createConstant("a")
    val z, b, c, d = createConstant

    import IExpression._

    setConstructProofs(true)

    scope {
      setPartitionNumber(1)
      !! (x === cons(y, z))
      setPartitionNumber(2)
      !! (x === nil())

      println(???)
      println(getInterpolants(List(Set(1), Set(2))))
    }

    scope {
      setPartitionNumber(1)
      !! (x === cons(y, z))
      !! (y > 0)
      setPartitionNumber(2)
      !! (head(x) === 0)

      println(???)
      println(getInterpolants(List(Set(1), Set(2))))
    }

    scope {
      setPartitionNumber(1)
      !! (x === cons(y, z))
      !! (y === 42)
      setPartitionNumber(2)
      !! (x === cons(a, b))
      !! (a === 43)

      println(???)
      println(getInterpolants(List(Set(1), Set(2))))
    }

    scope {
      setPartitionNumber(1)
      !! (x === cons(y, z))
      !! (y === 42)
      setPartitionNumber(2)
      !! (a === cons(head(x) - 1, x))
      setPartitionNumber(3)
      !! (a === cons(c, d))
      !! (c === 43)

      println(???)
      println(getInterpolants(List(Set(1), Set(2), Set(3))))
    }

    scope {
      setPartitionNumber(1)
      !! (x === nil())
      setPartitionNumber(2)
      !! (y === nil())
      setPartitionNumber(3)
      ?? (x === y)
      
      println(???)
      println(getInterpolants(List(Set(1), Set(2), Set(3))))
    }

    scope {
      setPartitionNumber(1)
      !! (x === cons(1, cons(2, nil())))
      setPartitionNumber(2)
      !! (y === cons(1, cons(2, nil())))
      setPartitionNumber(3)
      ?? (x === y)
      
      println(???)
      println(getInterpolants(List(Set(1), Set(2), Set(3))))
    }
  }
