// This example previously led to a typing error

\functions {
  bool f(int);
}

\problem {
  \forall int x; f(x) = (x % 2 = 0)
->
  f(42) = true
}
