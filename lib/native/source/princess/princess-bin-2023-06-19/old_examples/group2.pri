\functions {
  int e;
  int f(int, int);
  int i(int);
}

\problem {
  \forall int x; f(e, x) = x
->
  \forall int x; f(x, e) = x
->
  \forall int x; f(x, i(x)) = e
->
  \forall int x; f(i(x), x) = e
->
  \forall int x, y, z; f(x, f(y, z)) = f(f(x, y), z)
->
  \forall int x; \exists int y; f(x, f(y, e)) = e
//  \forall int x1, x2, x3, x4; f(x1, f(x2, f(x3, x4))) = f(f(f(x1, x2), x3), x4)
//  \forall int x, y; \exists int z; f(x, z) = y
}
