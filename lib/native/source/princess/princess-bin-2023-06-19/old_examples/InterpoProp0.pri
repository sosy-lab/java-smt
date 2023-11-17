\predicates {
  /* Declare predicates occurring in the problem
   * (implicitly universally quantified)
   *
   * r(int, int); p(int); q;
   */
  p; q; r;  
}

\problem {
\part[left]  (p -> q)
 & \part[right] ( !p -> r)
->
  \part[right] ((p & q) | (!p & r))
}

\interpolant { left; right }
