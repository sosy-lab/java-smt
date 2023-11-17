/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2016 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.theories._
import ap.proof.theoryPlugins.Plugin
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{Term, TerForConvenience, TermOrder}
import ap.terfor.preds.Atom
import ap.proof.goal.Goal


/**
 * Simple theory implementing associativity of a function symbol f.
 * This is done by: 1. using a triggered axiom to turn right-associative
 * occurrences into left-associative occurrences, and 2. using a plug-in
 * that eliminates remaining right-associative occurrences from goals.
 */
object ATheory extends Theory {
  import IExpression._

  val f = new IFunction("f", 2, true, false)
  val functions = List(f)

  val (predicates, axioms, _, functionTranslation) =
    Theory.genAxioms(theoryFunctions = functions,
                     theoryAxioms =
                       all(x => all(y => all(z =>
                           trig(f(f(x, y), z) === f(x, f(y, z)),
                              f(x, f(y, z)))))))
  val Seq(_f) = predicates
  val totalityAxioms = Conjunction.TRUE

  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions : Set[IFunction] = Set()
  val functionalPredicates = predicates.toSet
  val functionPredicateMapping = List(f -> _f)

  //////////////////////////////////////////////////////////////////////////////

  val plugin = Some(new Plugin {
    // not used
    def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] = None

    override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      val fAtoms = goal.facts.predConj.positiveLitsWithPred(_f)

      val atomsToRemove =
        for (a1 <- fAtoms.iterator;             // f(a,   f(b, c))
             a2 <- fAtoms.iterator;             // a1     a2
             if (a1(1) == a2(2) &&
                 (fAtoms exists {               // f(  f(a, b), c)
                    a3 => a3(1) == a2(1) &&     // a3  a4
                          a3(2) == a1(2) &&
                          (fAtoms exists {
                             a4 => a4(0) == a1(0) &&
                                   a4(1) == a2(0) &&
                                   a4(2) == a3(0)
                  })}))) yield a1

      val factsToRemove = Conjunction.conj(atomsToRemove, goal.order)
      if (factsToRemove.isTrue)
        List()
      else
        List(Plugin.RemoveFacts(factsToRemove))
    }
  })

  TheoryRegistry register this
}

////////////////////////////////////////////////////////////////////////////////

SimpleAPI.withProver(enableAssert = true) { p =>
  import p._
  import IExpression._
  import ATheory.f

  val a = createConstant("a")
  val x = createConstants(15)

  scope {
    val left = x reduceLeft (f(_, _))
    val right = x reduceRight (f(_, _))

    !! (left >= a)
    !! (right < a)
    println(???)
  }

}
