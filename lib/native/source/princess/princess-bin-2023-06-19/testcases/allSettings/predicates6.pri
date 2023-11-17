\predicates {
  p(int);
}

\functions {
  int x;
}

\problem {
  x >= 0 & x <= 3 & p(x)
->
  p(0) | p(1) | p(2) | p(3)
}