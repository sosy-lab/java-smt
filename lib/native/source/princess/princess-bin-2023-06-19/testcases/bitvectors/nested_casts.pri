/**
 * Check that nested casts are correctly parsed and handled
 */

\functions {
  int x;
}

\problem {
  x.\as[signed bv[8]].\as[int] = x <-> x >= -128 & x <= 127
}
