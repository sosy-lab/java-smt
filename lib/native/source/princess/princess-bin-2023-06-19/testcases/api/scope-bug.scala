import ap._
import ap.parser._

SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._


reset
val c0 = createConstant("c0")
val c1 = createConstant("c1")
val c2 = createConstant("c2")
!! (!(((c0 === 0) & (c1 === 0)) & (c2 === 0)))

scope {
!! (((((c0 * 0) + (c1 * 0)) + (c2 * 0)) === 0))

scope {
!! (((((c1 * 1) - (c0*3)) + (c2 * 0)) === 0))
// ???
println("0: " + checkSat(true))

scope {
!! (((((c0 * 2) + (c1 * 0)) - c2) === 0))
// ???
println("1: " + checkSat(true))

scope {
!! (((((c1 * 1) - (c0*3)) + (c2 * 0)) === 0))
// ???
println("2: " + checkSat(true))

scope {
!! (((((c0 * 0) - (c1*2)) + (c2 * 3)) === 0))
// ???
println("3: " + checkSat(true))
// ???
println("4: " + eval(c0))
println("5: " + eval(c1))
println("6: " + eval(c2))
} // pop scope

} // pop scope

} // pop scope

!! (((((c0 * 1) + (c1 * 3)) + (c2 * 2)) === 0))
// ???
println("7: " + checkSat(true))

scope {
!! (((((c0 * 2) + (c1 * 0)) - c2) === 0))
// ???
println("8: " + checkSat(true))
} // pop scope

println("10b: " + checkSat(true))
println("11: " + eval(c0))
println("12: " + eval(c1))
println("13: " + eval(c2))

}}}