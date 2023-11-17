\functions {
  \partial int select(int, int);
  \partial int store(int, int, int);

  int i0, i1, i2, i0', i1', i2',
      j0, j1, j2, j0', j1', j2',
      A0, A1, A2, A3, A4,
      read0, read1, read0', read1',
      write0, write1, write0', write1';

  int id0, id1;
}

\predicates {
   T(int, int, int, int, int, int, int, int);
}

\problem {
  ////////////////////////////////////////////////////////////////////////////////
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

   \forall int i, i', j, j', A, A', read, write; (
     T(i, i', j, j', A, A', read, write)
     ->
     (i = i' &
      (j < 15 -> j' = j + 1) &
      (j = 15 -> j' = 0) &
      A' = store(A, i+j, select(A, i+j) + 1) & read = i+j & write = i+j)
   )

->

   \part[init] id0 != id1
->

   \part[stepAI] (i0 = 16*id0 & j0 = 0)
->
   \part[stepA0] T(i0, i1, j0, j1, A0, A1, read0, write0)
->
   \part[stepA1] T(i1, i2, j1, j2, A1, A2, read1, write1)
->
   \part[stepBI] (i0 = 16*id0 & j0 = 0)
->
   \part[stepB0] T(i0', i1', j0', j1', A2, A3, read0', write0')
->
   \part[stepB1] T(i1', i2', j1', j2', A3, A4, read1', write1')
->
   \part[assert] (read1 != write1' & read1' != write1)
}

/* Interpolation specification */
\interpolant { stepAI, stepA0; stepA1, stepBI, stepB0, stepB1, assert, init }
