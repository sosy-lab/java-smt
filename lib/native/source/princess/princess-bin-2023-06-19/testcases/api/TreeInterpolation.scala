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

// Unit test for tree interpolation functionality. Previously, when a
// formula was asserted repeatedly in a tree interpolation problem,
// sometimes incorrect interpolants were returned.

//package ap;

import ap.SimpleAPI
import ap.parser._
import ap.basetypes.Tree

//object TreeIntTest {
//  def main(args: Array[String]) =
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      import IExpression._

      setConstructProofs(true)

      val a = createConstant("a")
      val b = createConstant("b")
      val c = createConstant("c")
      val d = createConstant("d")
      val e = createConstant("e")

      val A =  a === 1
      val B =  a === b
      val R1 = b === c
      val C =  c === d + 1
      val R2 = d === e
      val D =  e === 5

      setPartitionNumber(1)
      !! (A)

      setPartitionNumber(10)
      !! (B)

      setPartitionNumber(2)
      !! (A)

      setPartitionNumber(20)
      !! (C)

      setPartitionNumber(3)
      !! (R1)

      setPartitionNumber(4)
      !! (A)

      setPartitionNumber(40)
      !! (D)

      setPartitionNumber(5)
      !! (R2)

      println(???)

      println(getUnsatCore.toList.sorted)

      getTreeInterpolant(
        Tree(Set(5),
             List(Tree(Set(3), List(
                       Tree(Set(1, 10), List()),
                       Tree(Set(2, 20), List())
                  )),
                  Tree(Set(4, 40), List())))).prettyPrint
  }
//}
