import ap._
import ap.parser._

SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._
{


reset
}
{
val c0 = createConstant("c0")
val c1 = createConstant("c1")

scope {
!! (c0 / 3 > 1)
println("0: " + ???)
println(partialModel)
!! (c0 < 8)
println("1: " + ???)
println(partialModel)
} // pop scope


scope {
?? (c0 / 4 <= c0 / 3)
println("2: " + ???)
println(partialModel)
} // pop scope


scope {
!! ((c0 >= 1))
!! ((c1 >= 1))
?? (c0 / c1 >= 1)
println("3: " + ???)
println(partialModel)
!! ((c0 >= c1))
println("4: " + ???)
} // pop scope


}} // withProver
