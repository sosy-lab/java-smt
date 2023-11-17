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
import ap.theories._
import ap.proof.theoryPlugins.Plugin
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{Term, TerForConvenience}
import ap.proof.goal.Goal

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet}

/**
 * Extremely naive implementation of a theory of non-linear integer arithmetic.
 * Currently the theory only does AC-congruence reasoning for multiplication.
 */
object MulTheory extends Theory {
  import IExpression._

  val mul = new IFunction("mul", 2, true, false)
  val _mul = new Predicate("_mul", 3)

  val functions = List(mul)
  val predicates = List(_mul)
  val axioms = Conjunction.TRUE
  val totalityAxioms = Conjunction.TRUE
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions : Set[IFunction] = Set()
  val functionalPredicates = predicates.toSet
  val functionPredicateMapping = List(mul -> _mul)

  //////////////////////////////////////////////////////////////////////////////

  val plugin = Some(new Plugin {
    override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {

      type TermMultiset = Map[Term, Int]

      def join(a : TermMultiset, b : TermMultiset) : TermMultiset = {
        var res = a
        for ((t, mult) <- b)
          res = res + (t -> (a.getOrElse(t, 0) + mult))
        res
      }

      // detect _mul facts in the goal

      val termDefs = new MHashMap[Term, MHashSet[TermMultiset]]
      for (a <- goal.facts.predConj.positiveLitsWithPred(_mul))
          termDefs.getOrElseUpdate(a(2), new MHashSet[TermMultiset]) +=
            join(Map(a(0) -> 1), Map(a(1) -> 1))

      val names = termDefs.keys.toList

      // fixed-point computation, to determine all products represented
      // by the individual terms

      var changed = true
      while (changed) {
        changed = false

        for (name <- names) {
          val products = termDefs(name)

          val newProducts =
            for (product <- products.iterator;
                 (t, mult) <- product.iterator;
                 if ((name != t) && (termDefs contains t));
                 tProduct <- termDefs(t).iterator)
            yield join(if (mult == 1)
                         product - t
                       else
                         product + (t -> (mult - 1)),
                       tProduct)

          val allProducts = products ++ newProducts
          if (products.size != allProducts.size) {
            changed = true
            termDefs.put(name, allProducts)
          }
        }
      }

//      println(termDefs.toList)

      // invert the termDefs mapping

      val productNames = new MHashMap[TermMultiset, MHashSet[Term]]
      for ((name, products) <- termDefs.iterator;
           product <- products.iterator)
        productNames.getOrElseUpdate(product, new MHashSet[Term]) += name

      // generate equations between different names representing the same
      // product

      import TerForConvenience._
      implicit val _ = goal.order

      val eqs =
        conj(for ((_, names) <- productNames.iterator;
                  Seq(name1, name2) <- names.iterator sliding 2)
             yield (name1 === name2))

//      println(eqs)

      if (eqs.isTrue)
        List()
      else
        List(Plugin.AddAxiom(List(), eqs, MulTheory.this))
    }
  })

  TheoryRegistry register this
}

////////////////////////////////////////////////////////////////////////////////

SimpleAPI.withProver(enableAssert = true) { p =>
  import p._
  import IExpression._
  import MulTheory.mul

  val a = createConstant("a")
  val b = createConstant("b")
  val c = createConstant("c")

  scope {
    !! (mul(a, b) >= c)
    !! (mul(b, a) < c)
    println(???)
  }

  scope {
    !! (mul(a, b) >= c)
    !! (mul(b, a) <= c)
    println(???)
    println(partialModel)
  }

  scope {
    !! (mul(a, mul(b, b)) >= c)
    !! (mul(b, mul(a, b)) < c)
    println(???)
  }

  scope {
    !! (c === mul(a, b))
    !! (mul(a, c) >= 0)
    !! (mul(b, mul(a, a)) < 0)
    println(???)
  }

}
