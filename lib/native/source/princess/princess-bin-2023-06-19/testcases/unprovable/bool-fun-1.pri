// This example previously led to an exception

\functions {
  bool f(int);
}

\problem {
  \forall int x; (f(x) <-> (x % 2 = 0))
->
  f(43) = true
}
