/**
 * Proof that certain disjunctions do not have to be
 * generated because of regularity reasons
 */

\functions {
  int a, b;
}

\predicates {
  p(int, int, int, int);
}

\problem {
  \forall int a, b, c, d; (p(a,b,a,b) -> p(a,b,c,d))
->
  (
    \exists int x; \forall int d; p(a, b, x, d)
  <->
    \exists int x; \forall int d; (p(a, b, x, d) | a=x & b!=d)
  )
}