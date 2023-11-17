/**
 * This problem caused wrong interpolants to be generated in some versions
 */

\functions {
  int i0, i1, i2, i0', i1', i2',
      j0, j1, j2, j0', j1', j2',
      A0, A1, A2, A3, A4, A5,
      read, read',
      write, write';

  int id, id';

  int a0, b0;
  int a1, b1;
}

\predicates {
   T(int, int,  // i
     int, int,  // j
     int, int,  // A
     int, int   // read, write
     );
   pre(int,  // id
       int,  // i
       int   // j
       );
}

\problem {
////////////////////////////////////////////////////////////////////////////////
// Program specification

   \forall int i, i', j, j', A, A', read, write; (
     T(i, i', j, j', A, A', read, write)
     ->
     i = i' &
     (j < 4 -> j' = j + 1) &
     (j = 4 -> j' = 0) &
     A' = A &
     (read = i+j | read = i+j') &
     write = i+j
   )

->

   \forall int id, i, j; (
     pre(id, i, j) -> i = 4*id & j = 0
   )

////////////////////////////////////////////////////////////////////////////////
// 1. Image computation


-> \part[init] id < id'
-> \part[initA] pre(id, i0, j0)
-> \part[stepA0] T(i0, i1, j0, j1, A0, A1, a0, b0)
-> \part[stepA1] T(i1, i2, j1, j2, A1, A2, a1, b1)
-> \part[stepAcheck] T(i1, i2, j1, j2, A2, A3, read, write)
-> \part[initB] pre(id', i0', j0')
-> \part[stepBcheck] T(i0', i1', j0', j1', A3, A4, read', write')
-> \part[assert] (write' != read & write' != write)


}

/* Interpolation specification */
\interpolant { initA, stepA0, stepA1; init, initB, stepAcheck, stepBcheck, assert }
