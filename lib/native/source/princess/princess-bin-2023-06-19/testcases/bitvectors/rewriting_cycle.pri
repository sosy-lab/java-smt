/**
 * A case that previously triggered a non-terminating loop in the
 * bit-vector rewriter.
 */

\functions {
  int 

   inv_main15_0_0,
    inv_main15_1_0,
   inv_main15_2_0,
  inv_main15_3_0,
   inv_main15_4_0,
  inv_main23_0_0,
   inv_main23_1_0,
    inv_main23_2_0,  
  inv_main23_3_0,
    inv_main23_4_0   

  ;

}

\problem {

  (inv_main23_4_0 + -1*inv_main15_4_0 = 0 &
 inv_main23_3_0 + inv_main23_1_0 + -2 = 0 &
 inv_main23_2_0 + -2 = 0 &
 inv_main23_0_0 + -1*inv_main15_0_0 = 0 &
 inv_main15_2_0 + -2 = 0 &
 -1*inv_main23_3_0 + inv_main15_0_0 >= 0 &
 -1*inv_main23_3_0 + 2147483647 >= 0 &
 inv_main23_3_0 + 2147483648 >= 0 &
 -1*inv_main23_1_0 + 2147483647 >= 0 &
 inv_main23_1_0 + 2147483648 >= 0 &
 -1*inv_main15_4_0 + 2147483647 >= 0 &
 inv_main15_4_0 + 2147483648 >= 0 &
 -1*inv_main15_3_0 + 2147483647 >= 0 &
 inv_main15_3_0 + 2147483648 >= 0 &
 -1*inv_main15_2_0 + 2147483647 >= 0 &
 inv_main15_2_0 + 2147483648 >= 0 &
 -1*inv_main15_1_0 + 2147483647 >= 0 &
 inv_main15_1_0 + 2147483648 >= 0 &
 -1*inv_main15_0_0 + 2147483647 >= 0 &
 (inv_main23_3_0 + 1).\as[signed bv[32]] = inv_main15_3_0 &
  (inv_main23_1_0 + inv_main15_3_0 + -1).\as[signed bv[32]] = inv_main15_1_0)

-> false
}
