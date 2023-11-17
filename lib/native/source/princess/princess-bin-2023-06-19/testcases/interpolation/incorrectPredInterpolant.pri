\functions {
  /* Declare constants and functions occurring in the problem
   * (implicitly universally quantified). */

   int t, t', c, d, e;
}
\predicates {
  /* Declare predicates occurring in the problem
   * (implicitly universally quantified)
   *
   * e.g., divides(int, int);  */
  p(int);
}
\problem {
  /* Problem to be proven and interpolated */

  \part[left] (d=0 & e=0)
->
  \part[right] (c + d >= 0 & c + e <= 1)
->
  \part[left] !p(0)
|
  \part[right] (c!=1 -> p(c))


 
/*
t=0 -> t'=0 ->
  t+t' <= 0 | t != 0 & t+t'+1 <= 0
|  t+t'+1 <= 0 | t+1 != 0 & t+t'+2 <= 0
*/
}

\interpolant { left; right }
