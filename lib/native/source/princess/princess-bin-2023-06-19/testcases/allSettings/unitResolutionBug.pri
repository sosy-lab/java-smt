
\functions {
  int a, b;
}

\predicates {
  p(int); q(int);
}

\problem {
  \forall int x; (p(x) -> q(x) -> false)
->
  p(a)
->
  q(b)
->
  (a=1 & b=1 | a=2 & b=2)
->
  false
}