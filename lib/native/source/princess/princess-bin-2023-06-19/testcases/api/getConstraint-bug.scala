/**
 * This example previously lead to the exception

     scala.MatchError: null
	at ap.parser.Internal2InputAbsy.ap$parser$Internal2InputAbsy$$convert(Internal2InputAbsy.scala:78)
	at ap.parser.Internal2InputAbsy$.apply(Internal2InputAbsy.scala:45)
	at ap.SimpleAPI.asIFormula(SimpleAPI.scala:1421)
	at ap.SimpleAPI.getConstraint(SimpleAPI.scala:2297)
     [...]
 */

import ap._
import ap.parser._
import ap.basetypes.IdealInt

SimpleAPI.withProver { p =>
import p._
import IExpression._
{


reset
}
{


scope {
val headVar0 = createConstant("headVar0")
val headVar1 = createConstant("headVar1")
val headVar2 = createConstant("headVar2")
val headVar3 = createConstant("headVar3")
val headVar4 = createConstant("headVar4")
val headVar5 = createConstant("headVar5")
val headVar6 = createConstant("headVar6")
val headVar7 = createConstant("headVar7")
val headVar8 = createConstant("headVar8")
val headVar9 = createConstant("headVar9")
val headVar10 = createConstant("headVar10")
val headVar11 = createConstant("headVar11")
val headVar12 = createConstant("headVar12")
val headVar13 = createConstant("headVar13")
val headVar14 = createConstant("headVar14")
val headVar15 = createConstant("headVar15")
val headVar16 = createConstant("headVar16")
val headVar17 = createConstant("headVar17")
val headVar18 = createConstant("headVar18")
val headVar19 = createConstant("headVar19")
val headVar20 = createConstant("headVar20")
val headVar21 = createConstant("headVar21")
val headVar22 = createConstant("headVar22")
val headVar23 = createConstant("headVar23")
val headVar24 = createConstant("headVar24")
val headVar25 = createConstant("headVar25")
val headVar26 = createConstant("headVar26")
val headVar27 = createConstant("headVar27")
val headVar28 = createConstant("headVar28")
val headVar29 = createConstant("headVar29")
val headVar30 = createConstant("headVar30")
val headVar31 = createConstant("headVar31")
val headVar32 = createConstant("headVar32")
val headVar33 = createConstant("headVar33")
val headVar34 = createConstant("headVar34")
val headVar35 = createConstant("headVar35")
val headVar36 = createConstant("headVar36")
val headVar37 = createConstant("headVar37")
val c0 = createConstant("c0") // addConstantRaw(c0)
val c1 = createConstant("c1") // addConstantRaw(c1)
val c10 = createConstant("c10") // addConstantRaw(c10)
val c11 = createConstant("c11") // addConstantRaw(c11)
val c12 = createConstant("c12") // addConstantRaw(c12)
val c13 = createConstant("c13") // addConstantRaw(c13)
val c14 = createConstant("c14") // addConstantRaw(c14)
val c15 = createConstant("c15") // addConstantRaw(c15)
val c16 = createConstant("c16") // addConstantRaw(c16)
val c17 = createConstant("c17") // addConstantRaw(c17)
val c18 = createConstant("c18") // addConstantRaw(c18)
val c19 = createConstant("c19") // addConstantRaw(c19)
val c2 = createConstant("c2") // addConstantRaw(c2)
val c20 = createConstant("c20") // addConstantRaw(c20)
val c21 = createConstant("c21") // addConstantRaw(c21)
val c22 = createConstant("c22") // addConstantRaw(c22)
val c23 = createConstant("c23") // addConstantRaw(c23)
val c24 = createConstant("c24") // addConstantRaw(c24)
val c25 = createConstant("c25") // addConstantRaw(c25)
val c26 = createConstant("c26") // addConstantRaw(c26)
val c27 = createConstant("c27") // addConstantRaw(c27)
val c28 = createConstant("c28") // addConstantRaw(c28)
val c29 = createConstant("c29") // addConstantRaw(c29)
val c3 = createConstant("c3") // addConstantRaw(c3)
val c30 = createConstant("c30") // addConstantRaw(c30)
val c31 = createConstant("c31") // addConstantRaw(c31)
val c32 = createConstant("c32") // addConstantRaw(c32)
val c33 = createConstant("c33") // addConstantRaw(c33)
val c34 = createConstant("c34") // addConstantRaw(c34)
val c35 = createConstant("c35") // addConstantRaw(c35)
val c36 = createConstant("c36") // addConstantRaw(c36)
val c37 = createConstant("c37") // addConstantRaw(c37)
val c4 = createConstant("c4") // addConstantRaw(c4)
val c5 = createConstant("c5") // addConstantRaw(c5)
val c55 = createConstant("c55") // addConstantRaw(c55)
val c56 = createConstant("c56") // addConstantRaw(c56)
val c6 = createConstant("c6") // addConstantRaw(c6)
val c7 = createConstant("c7") // addConstantRaw(c7)
val c8 = createConstant("c8") // addConstantRaw(c8)
val c9 = createConstant("c9") // addConstantRaw(c9)

scope {
makeExistential(headVar0)
makeExistential(headVar1)
makeExistential(headVar2)
makeExistential(headVar3)
makeExistential(headVar4)
makeExistential(headVar5)
makeExistential(headVar6)
makeExistential(headVar7)
makeExistential(headVar8)
makeExistential(headVar9)
makeExistential(headVar10)
makeExistential(headVar11)
makeExistential(headVar12)
makeExistential(headVar13)
makeExistential(headVar14)
makeExistential(headVar15)
makeExistential(headVar16)
makeExistential(headVar17)
makeExistential(headVar18)
makeExistential(headVar19)
makeExistential(headVar20)
makeExistential(headVar21)
makeExistential(headVar22)
makeExistential(headVar23)
makeExistential(headVar24)
makeExistential(headVar25)
makeExistential(headVar26)
makeExistential(headVar27)
makeExistential(headVar28)
makeExistential(headVar29)
makeExistential(headVar30)
makeExistential(headVar31)
makeExistential(headVar32)
makeExistential(headVar33)
makeExistential(headVar34)
makeExistential(headVar35)
makeExistential(headVar36)
makeExistential(headVar37)
setMostGeneralConstraints(true)
?? (!((!(c36 === 0) & (((c37 === 0) & (c36 === 0)) & (c25 === 0))) & ((((((((((((((((((((((((((((((((((((((c0 === headVar0) & (c1 === headVar1)) & (c2 === headVar2)) & (c3 === headVar3)) & (c4 === headVar4)) & (c5 === headVar5)) & (c6 === headVar6)) & (c7 === headVar7)) & (c8 === headVar8)) & (c9 === headVar9)) & (c10 === headVar10)) & (c11 === headVar11)) & (c12 === headVar12)) & (c13 === headVar13)) & (c14 === headVar14)) & (c15 === headVar15)) & (c16 === headVar16)) & (c17 === headVar17)) & (c18 === headVar18)) & (c19 === headVar19)) & (c20 === headVar20)) & (c21 === headVar21)) & (c22 === headVar22)) & (c23 === headVar23)) & (c24 === headVar24)) & (c25 === headVar25)) & (c26 === headVar26)) & (c27 === headVar27)) & (c28 === headVar28)) & (c29 === headVar29)) & (c30 === headVar30)) & (c31 === headVar31)) & (c32 === headVar32)) & (c33 === headVar33)) & (c34 === headVar34)) & (c35 === headVar35)) & (c36 === headVar36)) & (c37 === headVar37))))
println("39: " + ???)
println("40: " + getConstraint)
} // pop scope

} // pop scope


}} // withProver
