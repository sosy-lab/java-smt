/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2014 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.basetypes.IdealInt
import ap.parser._
import ap.proof.goal.Goal
import ap.terfor.{TerForConvenience, Formula}
import ap.terfor.preds.{Atom, Predicate}
import ap.terfor.conjunctions.Conjunction
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}

import scala.collection.mutable.ArrayBuffer

object SimpleAPITest6 extends App {
  ap.util.Debug.enableAllAssertions(true)
  val p = SimpleAPI.spawnWithAssertions
  
  import IExpression._
  import SimpleAPI.ProverStatus
  import p._

  val square = createFunction("square", 1)
  val squarePred = asConjunction(square(0) === 0).predicates.iterator.next

  //////////////////////////////////////////////////////////////////////////////

  /**
   * A procedure systematically splitting over the input domain
   * of the square function
   */
  object Splitter extends TheoryProcedure {
    def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      implicit val _ = goal.order
      import TerForConvenience._

      val squareLits = goal.facts.predConj.positiveLitsWithPred(squarePred)
      val aConj = conj(goal.facts.arithConj)

      val splits = new ArrayBuffer[(Conjunction, Conjunction, IdealInt)]

      for (a <- squareLits) {
        (PresburgerTools.lowerBound(a(0), aConj),
         PresburgerTools.lowerBound(-a(0), aConj)) match {
          case (Some(lb), Some(ubM)) if (lb == -ubM) =>
            // nothing
          case (Some(lb), Some(ubM)) => {
            val sum = lb - ubM
            val thres = sum.signum match {
              case -1 => -((-sum + 1) / 2)
              case _ => sum / 2
            }
            splits += ((a(0) <= thres, a(0) > thres, thres))
          }
          case (Some(lb), None) if (lb.signum >= 0) => {
            val thres = (lb + 1) * 2
            splits += ((a(0) <= thres, a(0) > thres, thres))
          }
          case (None, Some(ubM)) if (ubM.signum >= 0) => {
            val thres = (-ubM - 1) * 2
            splits += ((a(0) > thres, a(0) <= thres, thres))
          }
          case _ => {
            splits += ((a(0) <= 0, a(0) > 0, 0))
          }
        }
      }

      if (splits.isEmpty) {
        List()
      } else {
        val (left, right, _) = splits.toList minBy (_._3.abs)
        List(Plugin.SplitGoal(List(List(Plugin.AddFormula(!left)),
                                   List(Plugin.AddFormula(!right)))))
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * (Forward) interval propagation for the square function
   */
  object Propagator extends Plugin {
    def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] = None
    
    override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      implicit val _ = goal.order
      import TerForConvenience._

      val squareLits = goal.facts.predConj.positiveLitsWithPred(squarePred)
      val aConj = conj(goal.facts.arithConj)

      val newBounds = new ArrayBuffer[Formula]
      for (a <- squareLits) {
        newBounds += (a(1) >= 0)

        (PresburgerTools.lowerBound(a(0), aConj),
         PresburgerTools.lowerBound(-a(0), aConj)) match {
          case (Some(lb), Some(ubM)) if (lb.signum >= 0) => {
            newBounds += (a(1) >= (lb * lb))
            newBounds += (a(1) <= (ubM * ubM))
          }
          case (Some(lb), Some(ubM)) if (ubM.signum >= 0) => {
            newBounds += (a(1) <= (lb * lb))
            newBounds += (a(1) >= (ubM * ubM))
          }
          case (Some(lb), Some(ubM)) => {
            val bMax = lb max ubM.abs
            newBounds += (a(1) <= (bMax * bMax))
          }
          case (Some(lb), None) if (lb.signum >= 0) => {
            newBounds += (a(1) >= (lb * lb))
          }
          case (None, Some(ubM)) if (ubM.signum >= 0) => {
            newBounds += (a(1) >= (ubM * ubM))
          }
          case _ => {
            // nothing
          }
        }

        // similarly, backward propagation could be implemented ...
      }

      val newFor = goal reduceWithFacts conj(newBounds)

      if (newFor.isTrue) {
        if (squareLits forall { a => a(0).isConstant })
          List()
        else
          // schedule splitting as a delayed task
          List(Plugin.ScheduleTask(Splitter, 0))
      } else {
        List(Plugin.AddFormula(!newFor))
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  setupTheoryPlugin(Propagator)

  val x = createConstant("x")
  val k = createConstant("k")

  scope {
    !! (square(x) >= 100)
    !! (x >= 3)

    println(???)  // Sat

    !! (x <= 5)
    println(???)  // Unsat
  }

  scope {
    !! (k >= 0)
    !! (square(x) === 100 + k * 5)
    !! (x >= 3)

    println(???)                                    // Sat
    println("x = " + eval(x) + ", k = " + eval(k))  // x = 10, k = 0

    !! (x =/= eval(x))
    println(???)                                    // Sat
    println("x = " + eval(x) + ", k = " + eval(k))  // x = 15, k = 25
  }

  p.shutDown
}
