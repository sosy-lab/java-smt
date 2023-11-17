// This example previously led to a hanging prover when
// calling "partialModel"

import ap.parser._
import ap.SimpleAPI

println("starting")

val p = SimpleAPI.spawnWithAssertions
import p._

val x = createBooleanVariable

push

println(???)

println("getting model ...")
println(partialModel)
println("finished")