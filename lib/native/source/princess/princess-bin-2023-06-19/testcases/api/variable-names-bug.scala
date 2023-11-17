/**
 * This problem should be sat, but previously gave the result unsat
 * since some of the monomial orderings relied on distinct variable names
 */

import ap._
import ap.parser._
import ap.basetypes.IdealInt

SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._
{


reset
}
{

scope {

val Xs = for (_ <- 0 until 2) yield createConstant("X")
// val Xs = for (n <- 0 until 2) yield createConstant("X" + n)

// addConstantRaw(x)
val x = createConstant("x")
// addConstantRaw(y)
val y = createConstant("y")
!! (IBoolLit(true))
!! (IBoolLit(true))
!! (Xs === List(x, y))
// addConstantRaw(__eval0)
val __eval0 = createConstant("__eval0")
// addConstantRaw(arg0)
val arg0 = createConstant("arg0")
!! ((((((mult(__eval0, __eval0) - __eval0) >= 1) & (IIntLit(IdealInt("100")) >= __eval0)) & (__eval0 >= 1)) & (mult(__eval0, __eval0) === arg0)))
!! (Xs === List(__eval0, arg0))
println("0: " + ???)
} // pop scope


}} // withProver
