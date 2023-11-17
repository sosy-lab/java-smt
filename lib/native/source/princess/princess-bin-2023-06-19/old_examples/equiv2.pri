/**
 * Proof that certain disjunctions do not have to be
 * generated because of regularity reasons
 */

\functions {
  int a, b, c;
}

\predicates {
  p(int, int, int, int, int, int);
}

\problem {
  \forall int a, b, c, d, e, f; (p(a,b,c,a,b,c) -> p(a,b,c,d,e,f))
->

  (
    \exists int x, y; \forall int d; p(a, b, c, x, y, d)
  <->
    \exists int x, y; \forall int d; (p(a, b, c, x, y, d) | a=x & b=y & c!=d)
  )
  &
  (
    \exists int x; \forall int d, e; p(a, b, c, x, d, e)
  <->
    \exists int x; \forall int d, e; (p(a, b, c, x, d, e) | a=x & (b!=d | c!=e))
  )
  &
  (
    \forall int d, e, f; p(a, b, c, d, e, f)
  <->
    \forall int d, e, f; (p(a, b, c, d, e, f) | (a!=d | b!=e | c!=f))
  )


/*

  Does not seem to hold:

  (
    \exists int x, y, z; p(a, b, c, x, y, z)
  <->
    \exists int x, y, z; (p(a, b, c, x, y, z) | a=x & b=y & c=z)
  )

*/
}