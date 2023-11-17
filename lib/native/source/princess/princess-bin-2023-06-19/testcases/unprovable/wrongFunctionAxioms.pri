\functions {
  int f(int);
}

\problem {
  \forall int x, y; (x <= y -> f(x) <= f(y))
->
  \forall int x; f(x) <= f(x-1)
}