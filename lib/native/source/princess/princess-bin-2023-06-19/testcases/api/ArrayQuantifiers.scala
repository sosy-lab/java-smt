// Test case that verifies that asserting quantified array formulas
// correctly produces the result Inconclusive

import ap._
import ap.parser._
import ap.theories.ExtArray

SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._

val ar = ExtArray(List(Sort.Integer), Sort.Integer)

val a = createConstant("a", ar.sort)

!! (ar.select(a, 0) === 0)

println(???) // Sat

!! (all(x => ar.select(a, x) === x))

println(???) // Inconclusive

!! (ar.select(a, 1) === 2)

println(???) // Unsat

}
