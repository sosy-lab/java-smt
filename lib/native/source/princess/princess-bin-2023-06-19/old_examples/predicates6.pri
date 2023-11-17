
\predicates {
  /* Declare predicates occurring in the problem
   * (implicitly universally quantified)
   *
   * r(int, int); p(int); q;
   */
  P(int); lt(int, int);
}

\problem {
  /* Problem to be proven
   *
   * \exists int a; (r(a, x) & a>=0) |
   *   \forall int a, b; (q() -> a>b -> r(a, b))
   */
  \forall int x; (P(x) <-> x=-1 | x=1 | x=10)
->
  \forall int x, y; (lt(x,y) <-> x < y)
->
  \exists int x; (P(x) & lt(x, 5))
}
