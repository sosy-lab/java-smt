/**
 * This case previously led to an exception in proof construction
 */

\functions {
  int i1_3_0, i1_2_0, i1_1_0, i2_2_0;
}

\problem {
\part[p1] (i1_1_0 + -75 = 0) &
\part[p2] (-1*i2_2_0 + 255 >= 0 & i2_2_0 >= 0 & -1*i1_1_0 + 255 >= 0 & i1_1_0 >= 0 & ((i2_2_0 + 2).\as[bv[8]] = i1_1_0)) &
\part[p3] (-1*i1_3_0 + 255 >= 0 & i1_3_0 + -71 >= 0 & -1*i2_2_0 + 255 >= 0 & i2_2_0 >= 0 & ((i1_3_0 + 1).\as[bv[8]] = i2_2_0)) &
\part[p4] (i1_3_0 + -100 = 0)

-> false
}

\interpolant{p4; p3; p2; p1}
\interpolant{p1; p2; p3; p4}

