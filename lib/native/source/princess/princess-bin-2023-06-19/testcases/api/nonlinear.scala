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
!! (c0 ** c1 >= 4)
println("0: " + ???)
println(partialModel)
!! (c0 >= 3)
!! (c1 >= 3)
println("1: " + ???)
println(partialModel)
!! (c0 ** c1 < 7)
println("2: " + ???)
} // pop scope


scope {
?? (((c0 + 1) ^ 2) >= (c0 ^ 2))
println("3: " + ???)
println(partialModel)
!! (c0 >= 0)
println("4: " + ???)
} // pop scope

scope {
?? (c0 ** c1 === c1 ** c0)
println("5: " + ???)
} // pop scope

}}
