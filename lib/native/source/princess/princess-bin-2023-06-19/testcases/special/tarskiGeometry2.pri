\functions {
  int a, b, c, d;
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

/*
  \forall int x, y; (bw(x, y, x) -> x=y)
->
  \forall int x, y, z, u, v; (bw(x, u, z) -> bw(y, v, z) ->
                              \exists int a; (bw(u, a, y) & bw(v, a, x)))
->
  //
  // axiom left out: continuity
  //
  \exists int a, b, c; (!bw(a,b,c) & !bw(b,c,a) & !bw(c,a,b))
->
  \forall int x, y, z, u, v; (cg(x,u,x,v) & cg(y,u,y,v) & cg(z,u,z,v) & u != v
                              -> (bw(x,y,z) | bw(y,z,x) | bw(z,x,y)))
->
  \forall int x, y, z, u, v, w; (bw(x,y,w) & cg(x,y,y,w) &
                                 bw(x,u,v) & cg(x,u,u,v) &
                                 bw(y,u,z) & cg(y,u,u,z) -> cg(y,z,v,w))
->*/ 

  //cg(a, b, a, b)
  cg(a, b, c, d) -> cg(a, b, d, c)
}
