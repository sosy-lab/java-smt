/**
 * Example that previously led to an exception in SimpleAPI.projectEx
 */

//package ap

import ap.parser._
import IExpression._
import ap.SimpleAPI
import ap.theories.ADT

//object Inconc extends App {
ap.util.Debug.enableAllAssertions(true)
val p = SimpleAPI.spawnWithAssertions
  import p._


val quans = List(
  (Quantifier.EX, Sort.Integer),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.Integer),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.Integer),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.Integer),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.Integer),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.Integer),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.Integer),
 (Quantifier.EX, Sort.Integer),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.Bool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.Integer),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool)).reverse



val f = quanWithSorts(quans,

  (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((ADT.BoolADT.False === IVariable(8, Sort.Bool)) & !(IVariable(6, Sort.MultipleValueBool) === 0)) & !(IVariable(39, Sort.MultipleValueBool) === 0)) & (IVariable(39, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(53, Sort.MultipleValueBool) === 0)) & !(IVariable(41, Sort.MultipleValueBool) === 0)) & (IVariable(41, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(28, Sort.MultipleValueBool) === 0)) & !(IVariable(14, Sort.MultipleValueBool) === 0)) & (IVariable(14, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(45, Sort.MultipleValueBool) === 0)) & !(IVariable(31, Sort.MultipleValueBool) === 0)) & (IVariable(31, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(29, Sort.MultipleValueBool) === 0)) & !(IVariable(4, Sort.MultipleValueBool) === 0)) & (IVariable(4, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(33, Sort.MultipleValueBool) === 0)) & !(0 === IVariable(34))) & !(IVariable(20, Sort.MultipleValueBool) === 0)) & (IVariable(20, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(3, Sort.MultipleValueBool) === 0)) & !(IVariable(9, Sort.MultipleValueBool) === 0)) & (IVariable(9, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(25, Sort.MultipleValueBool) === 0)) & !(IVariable(1, Sort.MultipleValueBool) === 0)) & (IVariable(1, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(22, Sort.MultipleValueBool) === 0)) & !(IVariable(19, Sort.MultipleValueBool) === 0)) & (IVariable(19, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(36, Sort.MultipleValueBool) === 0)) & !(IVariable(49, Sort.MultipleValueBool) === 0)) & (IVariable(49, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(18, Sort.MultipleValueBool) === 0)) & !(0 === IVariable(11))) & !(IVariable(52, Sort.MultipleValueBool) === 0)) & (IVariable(52, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(38, Sort.MultipleValueBool) === 0)) & !(IVariable(5, Sort.MultipleValueBool) === 0)) & (IVariable(5, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(7, Sort.MultipleValueBool) === 0)) & !(IVariable(27, Sort.MultipleValueBool) === 0)) & (IVariable(27, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(13, Sort.MultipleValueBool) === 0)) & !(IVariable(35, Sort.MultipleValueBool) === 0)) & (IVariable(35, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(16, Sort.MultipleValueBool) === 0)) & !(IVariable(0, Sort.MultipleValueBool) === 0)) & (IVariable(0, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(46, Sort.MultipleValueBool) === 0)) & !(IVariable(40, Sort.MultipleValueBool) === 0)) & (IVariable(40, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(51, Sort.MultipleValueBool) === 0)) & !(IVariable(44, Sort.MultipleValueBool) === 0)) & (IVariable(44, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(43, Sort.MultipleValueBool) === 0)) & (((IVariable(57) === 0) & (IVariable(15) === 0)) | (!(IVariable(57) === 0) & !(IVariable(15) === 0)))) & (((IVariable(56) === 0) & (IVariable(42) === 0)) | (!(IVariable(56) === 0) & !(IVariable(42) === 0)))) & (((IVariable(60) === 0) & (IVariable(10) === 0)) | (!(IVariable(60) === 0) & !(IVariable(10) === 0)))) & (((IVariable(58) === 0) & (IVariable(37) === 0)) | (!(IVariable(58) === 0) & !(IVariable(37) === 0)))) & (((IVariable(59) === 0) & (IVariable(47) === 0)) | (!(IVariable(59) === 0) & !(IVariable(47) === 0)))) & (((IVariable(61) === 0) & (IVariable(2) === 0)) | (!(IVariable(61) === 0) & !(IVariable(2) === 0)))) & !(IVariable(21, Sort.MultipleValueBool) === 0)) & (IVariable(43, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(30, Sort.MultipleValueBool) === 0)) & !(0 === IVariable(54))) & !(IVariable(12, Sort.MultipleValueBool) === 0)) & (IVariable(12, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(50, Sort.MultipleValueBool) === 0)) & !(IVariable(23, Sort.MultipleValueBool) === 0)) & (IVariable(23, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(32, Sort.MultipleValueBool) === 0)) & !(IVariable(24, Sort.MultipleValueBool) === 0)) & (IVariable(24, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(26, Sort.MultipleValueBool) === 0)) & !(IVariable(17, Sort.MultipleValueBool) === 0)) & (IVariable(17, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(48, Sort.MultipleValueBool) === 0)))

println(simplify(f))

//}
