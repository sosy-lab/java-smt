/**
 * Example that previously led to interpolants containing quantifiers
 */

\functions {
 int inv_main4_3_1, inv_main4_3_0, inv_main4_2_1, inv_main4_2_0, inv_main4_1_b_1, inv_main4_1_b_0, inv_main4_1_1, inv_main4_1_0, inv_main4_1_a_1, inv_main4_1_a_0
  , local0, local1;
}

\problem {
    \part[part0] (
  inv_main4_1_1 + inv_main4_1_0 - inv_main4_1_a_1 = inv_main4_1_a_0 & -1 >=
  inv_main4_1_a_1 & inv_main4_1_a_1 >= -2147483648 & 0 >= inv_main4_1_a_0 &
  inv_main4_1_a_0 >= -2147483648
) &
  \part[part1] (
  inv_main4_2_0 >= 2*local0 & 2*local0 - inv_main4_2_0 >= -1 & 2147483647 >=
  inv_main4_2_1 & inv_main4_2_1 >= -2147483648 & 2147483647 >= inv_main4_2_0 &
  inv_main4_2_0 >= 1 & inv_main4_1_1 - inv_main4_1_b_0 + inv_main4_1_0 >=
  -2147483648 & 2147483647 >= inv_main4_1_b_0 & inv_main4_1_b_0 - inv_main4_1_1
  - inv_main4_1_0 >= -2147483647 & inv_main4_1_b_0 >= -2147483648 &
  inv_main4_2_0[0:0]= 1 & local0.\as[signed bv[32]] =
    inv_main4_1_b_0 & (inv_main4_2_1 + 1).\as[signed bv[32]] =
    inv_main4_1_1 - inv_main4_1_b_0 + inv_main4_1_0
//   &  local0 >= -2147483648 & local0 <= 2147483647
) &
  \part[part2] (
  inv_main4_3_0 >= 2*local1 & 2*local1 - inv_main4_3_0 >= -1 & 2147483647 >=
  inv_main4_3_1 & inv_main4_3_1 >= -2147483648 & 2147483647 >= inv_main4_3_0 &
  inv_main4_3_0 >= 1 & 2147483647 >= inv_main4_2_1 & inv_main4_2_1 >=
  -2147483648 & 2147483647 >= inv_main4_2_0 & inv_main4_2_0 >= -2147483648 &
  inv_main4_3_0[0:0]= 1 & local1.\as[signed bv[32]] =
    inv_main4_2_0 & (inv_main4_3_1 + 1).\as[signed bv[32]] =
    inv_main4_2_1
) &
  \part[part3] (
  inv_main4_3_1 = 0 & 2147483647 >= inv_main4_3_0 & inv_main4_3_0 >= -2147483648
)

-> false
}

\interpolant{part0; part1; part2; part3}
