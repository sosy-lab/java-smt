\functions {
  \partial int select(int, int);
  \partial int store(int, int, int);

  int nondet;

  int i_copy'0, ctr_copy'0, index'0, mark'0, prres0'0, location'0, prres0_skip'0;
  int i_copy'1, ctr_copy'1, index'1, mark'1, prres0'1, location'1, prres0_skip'1;
  int i_copy'2, ctr_copy'2, index'2, mark'2, prres0'2, location'2, prres0_skip'2;
  int i_copy'3, ctr_copy'3, index'3, mark'3, prres0'3, location'3, prres0_skip'3;
  int i_copy'4, ctr_copy'4, index'4, mark'4, prres0'4, location'4, prres0_skip'4;
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

 // Partition at file <probity-instrumenter>
\part[p0] (  !\forall int i'0; (select(i_copy'1, i'0) = select(ctr_copy'1, i'0)
                            | !(i'0 > 0) | !(index'3 >= i'0)))
& // Partition at file <probity-instrumenter>
\part[p1] (  index'3 = -1 + index'2 & index'2 > 1 & select(mark'2,index'2) = 1)
& // Partition at file <probity-instrumenter>
\part[p2] (  select(prres0'2, index'2) = 1)
& // Partition at file <probity-instrumenter>
\part[p3] (  true)
& // Partition at file <probity-instrumenter>
\part[p4] (  true)
& // Partition at file <probity-instrumenter>
\part[p5] (  true)
& // Partition at file <probity-instrumenter>
\part[p6] (  select(prres0'2, index'2) = 1)
& // Partition at file <probity-instrumenter>
\part[p7] (  true)
& // Partition at file <probity-instrumenter>
\part[p8] (  prres0_skip'2 = 1)
& // Partition at file <probity-instrumenter>
\part[p9] (  prres0_skip'2 = nondet)
& // Partition at file <probity-instrumenter>
\part[p10] (  true)
& // Partition at file <probity-instrumenter>
\part[p11] (  true)
& // Partition at file <probity-instrumenter>
\part[p12] (  select(prres0'2, index'2) = 1)
& // Partition at file <probity-instrumenter>
\part[p13] (  true)
& // Partition at file <probity-instrumenter>
\part[p14] (  true)
& // Partition at file <probity-instrumenter>
\part[p15] (  prres0'2 = (store(prres0'1, index'2, 1)))
& // Partition at file <probity-instrumenter>
\part[p16] (  !(select(prres0'1, index'2) = 1))
& // Partition at file <probity-instrumenter>
\part[p17] (  true)
& // Partition at file <probity-instrumenter>
\part[p18] (  !(select(prres0'1, index'2) = 1))
& // Partition at file <probity-instrumenter>
\part[p19] (  true)
& // Partition at file <probity-instrumenter>
\part[p20] (  select(location'1, index'2) = 0 & index'2 > 0 &
  \forall int i'0; {select(i_copy'1, i'0)} (select(i_copy'1, i'0) < 3 | !(i'0 > 0) | !(index'2 >= i'0)) &
  \forall int i'0; {select(prres0'1, i'0)} (select(prres0'1, i'0) != 1 | !(i'0 > 0) | !(index'2 >= i'0)) &
  \forall int i'0; {select(location'1, i'0)} (select(location'1, i'0) = 0 | !(i'0 > 0) | !(index'2 >= i'0)) &
  \forall int i'0; {select(i_copy'1, i'0), select(ctr_copy'1, i'0)} (select(i_copy'1, i'0) = select(ctr_copy'1, i'0) | !(i'0 > 0) | !(index'2 >= i'0)))

->

 false

}

\interpolant {p0; p1; p2; p3; p4; p5; p6; p7; p8; p9; p10; p11; p12; p13; p14; p15; p16; p17; p18; p19; p20}
