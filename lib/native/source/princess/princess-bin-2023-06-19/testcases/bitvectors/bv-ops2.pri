\functions {
  bv[8] x, z;
}

\problem {
  z = (x & 0xF0.\as[bv[8]] | 3.\as[bv[8]]) & x[3:0] > 10

-> false
}
