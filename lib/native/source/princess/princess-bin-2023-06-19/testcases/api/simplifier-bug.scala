import ap._
import ap.parser._

SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._

val c = createConstant("c")

println((new Simplifier)(ex(x => x === 0)))
println((new Simplifier)(ex(x => x =/= 0)))   // this was simplified to false
println((new Simplifier)(all(x => x === 0)))
println((new Simplifier)(all(x => x =/= 0)))

println((new Simplifier)(ex(x => x === c)))
println((new Simplifier)(ex(x => x =/= c)))   // this was simplified to false
println((new Simplifier)(all(x => x === c)))
println((new Simplifier)(all(x => x =/= c)))

}
