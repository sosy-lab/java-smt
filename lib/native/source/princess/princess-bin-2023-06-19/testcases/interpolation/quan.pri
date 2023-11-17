\functions {
  int c;
}

\predicates {
  p(int);
}

\problem {
  \part[left] \forall int x; (p(x) -> x >= 0)
->
  \part[left] p(c)
->
  \part[right] c >= -10
}

\interpolant{left; right}