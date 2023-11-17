\functions {
  int a, b, c, x, i, j;
  \partial int select(int, int);
  \partial int store(int, int, int);

// Predicate for array equality, to implement extensionality. Because
// we want to match both on positive and negative occurrences of the
// predicate, we declare it as a function and encode positive
// occurrences as eqArrays(int, int) = 0, negative occurrences as
// eqArrays(int, int) != 0
  \partial \relational int eqArrays(int, int);
}

\problem {
////////////////////////////////////////////////////////////////////////////////
// Array axioms

  \forall int ar, ind, val;
     {store(ar, ind, val)}
//     {select(store(ar, ind, val), ind)}  // this might be chosen for more efficiency
                                           // (but is incomplete)
     select(store(ar, ind, val), ind) = val
->
  \forall int ar, ind1, ind2, val;
     {select(store(ar, ind1, val), ind2)}
     (ind1 != ind2 ->
      select(store(ar, ind1, val), ind2) = select(ar, ind2))
->
  \forall int ar1, ar2; {eqArrays(ar1, ar2)}
    (eqArrays(ar1, ar2) != 0 ->
     \exists int x; select(ar1, x) != select(ar2, x))
->
  \forall int ar1, ar2, x; {eqArrays(ar1, ar2), select(ar1, x)}
//                           {eqArrays(ar1, ar2), select(ar2, x)}  // seems enough to
                                                                   // have one trigger
    (eqArrays(ar1, ar2) = 0 -> select(ar1, x) = select(ar2, x))
->

////////////////////////////////////////////////////////////////////////////////

  (a = b -> eqArrays(a, b) = 0)
&
  (eqArrays(a, b)=0 -> select(a, x) = select(b, x))
&
  (eqArrays(a, a)=0)
&
  (eqArrays(a, b)=0 -> eqArrays(b, c)=0 -> eqArrays(a, c)=0)
&
  (eqArrays(a, b)=0 -> eqArrays(b, a)=0)
&
  (eqArrays(a, b)=0 -> eqArrays(store(a, x, i), store(b, x, i))=0)
&
  (eqArrays(store(a, x, i), store(b, x, j))=0 -> i = j)
}
