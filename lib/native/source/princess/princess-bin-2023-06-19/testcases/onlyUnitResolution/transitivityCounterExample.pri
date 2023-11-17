\universalConstants {
  int a, b;
}

\predicates {
  p(int, int);
}

\problem {
  b >= a & b <= a+3
->
  \forall int x, y, z; (p(x, y) -> p(y, z) -> p(x, z))
->
  p(a, a) & p(a, a+1) & p(a+1, a+2)
->
  p(a, b)
}
