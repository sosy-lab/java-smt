\functions {
  int ar;
  int select(int, int);
  int store(int, int, int);
}

\problem {
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
    \forall int ar, ar2, ind; (
      \forall int ind; {select(ar, ind)}
                       (select(ar, ind) >= 0 & select(ar, ind) < 1000)
    ->
      ar2 = store(ar, ind, 13)
    ->
      \forall int ind; (select(ar2, ind) >= 0 & select(ar2, ind) < 1000)
    )
}