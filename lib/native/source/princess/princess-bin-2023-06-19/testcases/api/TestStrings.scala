/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018 Philipp Ruemmer <ph_r@gmx.net>
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

// Some simple API tests for strings

//package ap.theories.strings

//object TestStrings extends App {
  import ap.SimpleAPI
  import SimpleAPI.ProverStatus
  import ap.parser._
  import ap.theories.strings.SeqStringTheory
  import ap.util.Debug

  Debug enableAllAssertions true

  val stringTheory = SeqStringTheory(256)
  import stringTheory._
  import IExpression._

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    val x, y, z = createConstant(StringSort)
    implicit val _ = decoderContext

    scope {
      !! (x === "abc")

      println(???)
      println("x = " + evalToTerm(x))
      println("x = \"" + asString(eval(x)) + "\"")

      !! (x ++ y ++ "xyz" === z)

      println(???)
      println("y = " + evalToTerm(y))
      println("z = " + evalToTerm(z))
      println("z = \"" + asString(eval(z)) + "\"")

      !! (y =/= "")

      println(???)
      println("y = " + evalToTerm(y))
      println("z = " + evalToTerm(z))
      println("z = \"" + asString(eval(z)) + "\"")

      !! (y === z)

      println(???)
    }

    scope {
      !! (x ++ y === y ++ x)
      !! (str_len(x) === 2)
      !! (str_len(y) === 5)
      !! (x =/= "")

      println(???)
      println("x = " + evalToTerm(x))
      println("y = " + evalToTerm(y))

      ?? (str_head(x) === str_head(str_tail(x)))

      println(???)
    }
  }

//}
