\predicates {
  /* Declare predicates occurring in the problem
   * (implicitly universally quantified)
   *
   * r(int, int); p(int); q;
   */
  p; q; r;  
}

\problem {
  (p -> q) & ( !p -> r)
->
  (p & q) | (!p & r)
}
