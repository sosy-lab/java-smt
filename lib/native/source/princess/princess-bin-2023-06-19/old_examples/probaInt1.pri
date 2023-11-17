\functions {
  \partial int select(int, int);
  \partial int store(int, int, int);

  int nondet;

  int i_copy'0, ctr_copy'0, index'0, mark'0, prres0'0, location'0, prres0_skip'0, probability'0;
  int i_copy'1, ctr_copy'1, index'1, mark'1, prres0'1, location'1, prres0_skip'1, probability'1;
  int i_copy'2, ctr_copy'2, index'2, mark'2, prres0'2, location'2, prres0_skip'2, probability'2;
  int i_copy'3, ctr_copy'3, index'3, mark'3, prres0'3, location'3, prres0_skip'3, probability'3;
  int i_copy'4, ctr_copy'4, index'4, mark'4, prres0'4, location'4, prres0_skip'4, probability'4;

  int i'1, i'2;
  int mass'1;
  int ctr'1;
  int b1'1;

  int return_value___CPROVER_prob_biased_coin1'1;

  \partial int POW(int, int);
}

\problem {

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

        \forall int x; {POW(2, x)} POW(2, x) = 2 * POW(2, x - 1)

->

 \part[p0]( // Partition at file <probity-instrumenter>
  !((POW(2, -1 + index'3)) >= probability'2)
 ) & \part[p1]( // Partition at file for1.c line 12 function main
  index'3 = 1 + index'2
 ) & \part[p2]( // Partition at file for1.c line 10 function main
  i'2 < 3
 ) & \part[p3]( // Partition at file for1.c line 10 function main
  true
 ) & \part[p4]( // Partition at file for1.c line 15 function main
  i'2 = 1 + i'1
 ) & \part[p5]( // Partition at file for1.c line 14 function main
  !(b1'1 = 1)
 ) & \part[p6]( // Partition at file <probity-instrumenter>
  b1'1 = return_value___CPROVER_prob_biased_coin1'1 & return_value___CPROVER_prob_biased_coin1'1 = select(prres0'1, index'2)
 ) & \part[p7]( // Partition at file <probity-instrumenter>
  !prres0_skip'1 = 1
 ) & \part[p8]( // Partition at file <probity-instrumenter>
  prres0_skip'1 = nondet & probability'2 = 2 * probability'1
 ) & \part[p9]( // Partition at file <probity-instrumenter>
  !(select(prres0'1, index'2)=1) &
  i'1 < 3 & 1 + i'1 = index'2 &
  select(prres0'1, index'2) != 1 &
  mass'1 = 0 & i'1 = ctr'1 &
  index'2 > 0 &
  (POW(2, -1 + index'2)) >= probability'1 &
  \forall int i'0; {select(i_copy'1, i'0)} (select(i_copy'1, i'0) < 3 | !(i'0 > 0) | !(index'2 >= i'0)) &
  \forall int i'0; {select(prres0'1, i'0)} (select(prres0'1, i'0) != 1 | !(i'0 > 0) | !(index'2 >= i'0)) &
  \forall int i'0; {select(location'1, i'0)} (select(location'1, i'0) = 0 | !(i'0 > 0) | !(index'2 >= i'0)) &
  \forall int i'0; {select(i_copy'1, i'0)} {select(ctr_copy'1, i'0)} (select(i_copy'1, i'0) = select(ctr_copy'1, i'0) | !(i'0 > 0) | !(index'2 >= i'0))
)

->

 false

}

\interpolant {p0; p1; p2; p3; p4; p5; p6; p7; p8; p9}
