// Not provable, because we don't specify functionality of
// the relations

\predicates {
  select(int, int, int);
  store(int, int, int, int);
}

\problem {
// Array axioms
	\forall int ar1, ar2, ind, val;
             (store(ar1, ind, val, ar2) -> select(ar2, ind, val))
->
	\forall int ar1, ar2, ind1, ind2, val1, val2;
             (store(ar1, ind1, val1, ar2) -> ind1 != ind2 -> 
              select(ar1, ind2, val2) -> select(ar2, ind2, val2))
->

    \forall int ar1, ar2, ind; (
      \forall int ind, val; (select(ar1, ind, val) -> val >= 0 & val < 1000)
    ->
      store(ar1, ind, 13, ar2)
    ->
      \forall int ind, val; (select(ar2, ind, val) -> val >= 0 & val < 1000)
    )
}
