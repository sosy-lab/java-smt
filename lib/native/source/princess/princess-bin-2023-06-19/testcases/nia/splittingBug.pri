\functions {
  /* Declare constants and functions occurring in the problem
   * (implicitly universally quantified).
   * The keyword "\partial" can be used to define functions without totality axiom,
   * while "\relational" can be used to define "functions" without functionality axiom. */
  int x1, x2, x3, x4, x5, x6, x7, x8, x9;
}

\problem {
  \distinct(x1, x2, x3, x4, x5, x6, x7, x8, x9) &
  \min(x1, x2, x3, x4, x5, x6, x7, x8, x9) >= 1 &
  \max(x1, x2, x3, x4, x5, x6, x7, x8, x9) <= 9

&

  (10*x1 + x2) * x3 = 10*x4 + x5
&
  (10*x4 + x5) + (10*x6 + x7) = 10*x8 + x9

-> false
}
