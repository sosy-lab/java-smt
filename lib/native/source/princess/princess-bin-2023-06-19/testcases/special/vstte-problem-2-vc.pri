\functions {
  int b(int);
  int a(int);
  int blength;
  int alength;
}

\problem {
  alength = blength
->
  \forall int x; (0 <= x & x < blength -> b(a(x))= x)
->
  \forall int q; (0 <= q & q < alength -> (\exists int w; (0 <= w & w < alength & a(w) = q)))
->
  \forall int x, y; (0 <= x & x < y & y < blength -> b(x) != b(y))
}
