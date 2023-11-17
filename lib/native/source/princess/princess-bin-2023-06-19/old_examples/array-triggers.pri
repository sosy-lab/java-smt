/**
 * An example in which both triggers of the second array axiom are needed
 */

\functions {
  int x, y, z, x2, y2, z2, ar;
  \partial int select(int, int);
  \partial int store(int, int, int);
}

\problem {
// Array axioms
  \forall int ar, ind, val; {store(ar, ind, val)}
    select(store(ar, ind, val), ind) = val
->
  \forall int ar, ind1, ind2, val; {select(store(ar, ind1, val), ind2)}
                                   {store(ar, ind1, val), select(ar, ind2)}
    (ind1 != ind2 -> select(store(ar, ind1, val), ind2) = select(ar, ind2))
->

   store(store(ar,1,y), 2, y2) = store(store(ar,1,z), 2, z2)
->
  y=z
}
