\functions {
  \partial int select(int, int);
  \partial int store(int, int, int);
  \partial int diff(int, int);

// Predicate for array equality, to implement extensionality. Because
// we want to match both on positive and negative occurrences of the
// predicate, we declare it as a function and encode positive
// occurrences as eqArrays(int, int) = 0, negative occurrences as
// eqArrays(int, int) != 0
  \partial \relational int eqArrays(int, int);

  int a, b, c;
}

\functions {
  int M, M', x;
}

\problem {

////////////////////////////////////////////////////////////////////////////////
// Array axioms

  \forall int ar, ind, val;
     {store(ar, ind, val)}
     select(store(ar, ind, val), ind) = val
->
  \forall int ar, ind1, ind2, val;
     {select(store(ar, ind1, val), ind2)}
     (ind1 != ind2 ->
      select(store(ar, ind1, val), ind2) = select(ar, ind2))
->
  \forall int ar1, ar2; {eqArrays(ar1, ar2)}
    (eqArrays(ar1, ar2) != 0 ->
     select(ar1, diff(ar1, ar2)) != select(ar2, diff(ar1, ar2)))
->
  \forall int ar1, ar2, x; {eqArrays(ar1, ar2), select(ar1, x)}
    (eqArrays(ar1, ar2) = 0 -> select(ar1, x) = select(ar2, x))
->
////////////////////////////////////////////////////////////////////////////////



  eqArrays(a, store(store(b, 1, 5), 2, 10)) = 0
->
  eqArrays(a, b) != 0
->
  diff(a, b) >= 0 & diff(a, b) <= 10

/*
  \part[A] (M' = store(M, a, x) & eqArrays(M, M') != 0) &
  \part[B] (b != c & select(M',b) != select(M,b) & select(M',c) != select(M,c))
->
  false
*/

// The following two implications do not hold:

/*
  \exists int x, y; (a = store(b, x, y) & eqArrays(a, b) != 0)
->
  diff(a, b) = diff(b, a) */


/*
  eqArrays(a, b) != 0
->
  select(a, diff(b, a)) != select(b, diff(b, a)) */
}

//\interpolant{A; B}
