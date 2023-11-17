\functions {
  int a, b;
}

\predicates {
  cg(int, int, int, int);
  bw(int, int, int);
}

\problem {
  \forall int x, y; cg(x, y, y, x)
->
  \forall int x, y, z; (cg(x, y, z, z) -> x=y)
->
  \forall int x, y, z, u, v, w; (cg(x, y, z, u) -> cg(x, y, v, w) -> cg(z, u, v, w))
->
  \forall int x, y; (bw(x, y, x) -> x=y)
->
  \forall int x, y, z, u, v; (bw(x, u, z) -> bw(y, v, z) ->
                              \exists int a; (bw(u, a, y) & bw(v, a, x)))
->
  cg(a, b, a, b)
}