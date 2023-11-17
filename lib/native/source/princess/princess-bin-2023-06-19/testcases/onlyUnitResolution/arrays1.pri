
\predicates {
  select(int, int, int);
  store(int, int, int, int);
}

\problem {
// Totality
	\forall int x1, x2; \exists int y; select(x1, x2, y)
->
	\forall int x1, x2, x3; \exists int y; store(x1, x2, x3, y)
->
// Functionality
	\forall int x1, x2, y1, y2; (select(x1, x2, y1) -> select(x1, x2, y2)
                                     -> y1 = y2)
->
	\forall int x1, x2, x3, y1, y2; (store(x1, x2, x3, y1)
                                         -> store(x1, x2, x3, y2)
                                         -> y1 = y2)
->
// Array axioms
	\forall int ar1, ar2, ind, val;
             (store(ar1, ind, val, ar2) -> select(ar2, ind, val))
->
	\forall int ar1, ar2, ind1, ind2, val1, val2;
             (store(ar1, ind1, val1, ar2) -> ind1 != ind2 -> 
              select(ar1, ind2, val2) -> select(ar2, ind2, val2))
->
	\forall int ar1, ar2, ind1, ind2, val1, val2;
             (store(ar1, ind1, val1, ar2) -> ind1 != ind2 -> 
              select(ar2, ind2, val2) -> select(ar1, ind2, val2))
->

    \forall int ar1, ar2, ind; (
      \forall int ind, val; (select(ar1, ind, val) -> val >= 0 & val < 1000)
    ->
      store(ar1, ind, 13, ar2)
    ->
      \forall int ind, val; (select(ar2, ind, val) -> val >= 0 & val < 1000)
    )
}