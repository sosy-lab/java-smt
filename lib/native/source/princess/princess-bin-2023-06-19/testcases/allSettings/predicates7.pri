\predicates {
  p(int, int);
}

\functions {
  int x;
}

\problem {
  x = 13
->
  p(x+1, 26)
->
  p(14, 2*x)
}