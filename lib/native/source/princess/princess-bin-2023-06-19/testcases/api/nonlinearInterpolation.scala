import ap._
import ap.parser._

SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._
{

val x, y = createConstant

setConstructProofs(true)

setPartitionNumber(1)
!! (x === 2)
setPartitionNumber(2)
!! (y === 3)
setPartitionNumber(3)
!! (x ** y < 0)

println(???)

println(getInterpolants(List(Set(1, 3), Set(2))))

}}
