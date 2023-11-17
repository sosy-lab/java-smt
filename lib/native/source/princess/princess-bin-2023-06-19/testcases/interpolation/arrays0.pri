\functions {
  /* Declare constants and functions occurring in the problem
   * (implicitly universally quantified). */

  \partial int select(int, int);
  \partial int store(int, int, int);

  int b1'1, b1'0;
  int prres0'0, prres0'1, prob_index'2, prob_index'1, prob_index'0;
  int prres0_skip'1;
  int nondet0;
  int b1_copy'1, b1_copy'0;
  int prob_location'1, prob_location'0;
}
\problem {
  /* Problem to be proven and interpolated */

  // Array axioms
        \forall int ar, ind, val;
             {select(store(ar, ind, val), ind)}
             select(store(ar, ind, val), ind) = val
->
        \forall int ar, ind1, ind2, val;
             {select(store(ar, ind1, val), ind2)}
             (ind1 != ind2 ->
              select(store(ar, ind1, val), ind2) = select(ar, ind2))
->

\part[p0] true

->

\part[p1] b1'1 = 0

->

\part[p2] b1'1 = select(prres0'1, prob_index'2)

->

\part[p3] prres0_skip'1 = 0

->

\part[p4] prres0_skip'1 = nondet0

->

\part[p5] select(prres0'1, prob_index'2) = 1   // BUG introduced by me

->

\part[p6] true

->

\part[p7]  (prres0'1 = store(prres0'0, prob_index'2, 0) &
b1_copy'1 = store(b1_copy'0, prob_index'2, b1'0) &
prob_location'1 = store(prob_location'0, prob_index'2, 0))

->

\part[p8] true

->

\part[p9] (prob_index'1 = 0 & prob_index'2 = 1 + prob_index'1)

->

false

}

/* Interpolation specification */
\interpolant {p0; p1; p2; p3; p4; p5; p6; p7; p8; p9}
