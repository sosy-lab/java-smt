import ap._
import ap.parser._

SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._


reset
val exit_fwd = createBooleanVariable("exit_fwd")
val r115__1 = createConstant("r115__1")
val knull__0 = createConstant("$null__0")
val kr321__1 = createConstant("$r321__1")
val javauiouPrintStreamkjavaulanguSystemkerr231__0 = createConstant("java.io.PrintStream$java.lang.System$err231__0")
val kheap__0 = createConstant("$heap__0")
val kfreshglobal_0__1 = createConstant("$freshglobal_0__1")
val kalloc__0 = createConstant("$alloc__0")
val kheap__1 = createConstant("$heap__1")
val kheap__2 = createConstant("$heap__2")
val ktype__0 = createConstant("$type__0")
val javaulanguStringBuilder__0 = createConstant("java.lang.StringBuilder__0")
val kr217__1 = createConstant("$r217__1")
val kr524__1 = createConstant("$r524__1")
val kr626__1 = createConstant("$r626__1")
val kreturn__1 = createConstant("$return__1")
val rootjthen_fwd = createBooleanVariable("root#then_fwd")
val r014__1 = createConstant("r014__1")
val kthis__0 = createConstant("$this__0")
val kin_parameter__0__0 = createConstant("$in_parameter__0__0")
val root_fwd = createBooleanVariable("root_fwd")

setConstructProofs(true)
setPartitionNumber(0)
!! (((!root_fwd | (((r014__1 === kthis__0) & (r115__1 === kin_parameter__0__0)) & rootjthen_fwd)) & root_fwd))

setPartitionNumber(1)
!! (((!rootjthen_fwd | (((((((((((((((((((((r115__1 === knull__0) & (kr321__1 === javauiouPrintStreamkjavaulanguSystemkerr231__0)) & true) & !(select(kheap__0, kfreshglobal_0__1, kalloc__0) === 0)) & (kheap__1 === store(kheap__0, kfreshglobal_0__1, kalloc__0, ITermITE(true, 0, 1)))) & (kheap__2 === store(kheap__1, kfreshglobal_0__1, ktype__0, javaulanguStringBuilder__0))) & (kr217__1 === kfreshglobal_0__1)) & !(kr217__1 === knull__0)) & true) & !(r115__1 === knull__0)) & true) & !(kr217__1 === knull__0)) & true) & !(kr524__1 === knull__0)) & true) & !(kr626__1 === knull__0)) & true) & !(kr321__1 === knull__0)) & true) & (kreturn__1 === 2)) & exit_fwd)) & (!rootjthen_fwd | root_fwd)))

setPartitionNumber(2)
!! (((!exit_fwd | true) & (!exit_fwd | rootjthen_fwd)))

println("0: " + checkSat(true))
println("1: " + getInterpolants(List(Set(0), Set(1), Set(2))))
}
