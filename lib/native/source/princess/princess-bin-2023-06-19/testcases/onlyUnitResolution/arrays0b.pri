\functions {
  int ar;
  int select(int, int);
  int store(int, int, int);
}

\existentialConstants {
  int res1, res2, res3;
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
	ar = store(store(store(0, 0, 13),
                                  1, 34),
                                  2, 123)
->
        select(ar, 0) = res1 &
        select(ar, 1) = res2 &
        select(ar, 2) = res3
}