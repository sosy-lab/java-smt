\functions {
  int a, b;
  int f(int);
  int g(int);
}

\problem {
  \forall int x; f(g(x)) = g(x)
->
  g(a) = b
->
  g(a) = f(b)
}