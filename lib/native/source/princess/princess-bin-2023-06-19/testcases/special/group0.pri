\functions {
  int e;
  \partial int f(int, int);
  int i(int);
}

\problem {
  \forall int x; {f(e, x)} f(e, x) = x
->
  \forall int x; {f(x, e)} f(x, e) = x
->
  \forall int x; {i(x)} f(x, i(x)) = e
->
  \forall int x; {i(x)} f(i(x), x) = e
->
  \forall int x, y, z; {f(x, f(y, z))} {f(f(x, y), z)} f(x, f(y, z)) = f(f(x, y), z)
->
  \forall int x; \exists int y; f(x, f(y, e)) = e
}
