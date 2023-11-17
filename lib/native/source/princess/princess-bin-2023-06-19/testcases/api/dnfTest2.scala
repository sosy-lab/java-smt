// This program previously led to an exception in
// DNFConverter.mbDNF

import ap._
import ap.parser._
import ap.theories.ModuloArithmetic
import ap.util.Debug

Debug enableAllAssertions true

SimpleAPI.withProver(enableAssert = true) { p =>
  import p._
  
  val x = createConstant("x", ModuloArithmetic.UnsignedBVSort(8))
  val f = (x <= 60 | x >= 62)
  println(DNFConverter mbDNF f)
}
