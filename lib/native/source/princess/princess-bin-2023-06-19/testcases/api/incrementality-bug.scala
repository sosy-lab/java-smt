// case that previously led to an exception, since a
// formula with incompatible term order was added to
// the ModelSearchProver

import ap._
import ap.parser._

SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._

{


scope {

val A2_0_2 = createConstant("A2_0_2") // addConstantRaw(A2_0_2)
val N = createConstant("N") // addConstantRaw(N)
val __eval0 = createConstant("__eval0") // addConstantRaw(__eval0)

println("59: " + ???)

println("72: " + eval(A2_0_2))

?? ((((__eval0 + 1) + ((N + 1) * -1)) === 0))
println("73: " + checkSat(true)) // checkSat(false)

} // pop scope


}} // withProver
