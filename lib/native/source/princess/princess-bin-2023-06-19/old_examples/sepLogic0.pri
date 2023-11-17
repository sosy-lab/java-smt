\existentialConstants {
  int X;
}

\predicates {
  disjoint(int, int);
  heapeq(int, int);
}

\functions {
  int emptyheap;
  \partial int select(int, int);
  \partial int store(int, int, int);
  \partial int heapsum(int, int);

  int i;
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
// Disjoint sum of heaps
        \forall int h1, h2; (
		disjoint(h1, h2) <->
                \forall int x; {select(h1, x)} {select(h2, x)}
			       (select(h1, x) = 0 | select(h2, x) = 0))
->
// Extensional equality
        \forall int h1, h2; (
		heapeq(h1, h2) <->
                \forall int x; // {select(h1, x)} {select(h2, x)}
			       (select(h1, x) = select(h2, x)))
->
	\forall int x; {select(emptyheap, x)} select(emptyheap, x) = 0
->
	\forall int h1, h2, x; {select(heapsum(h1, h2), x)}
		    	       select(heapsum(h1, h2), x) =
		    	       select(h1, x) + select(h2, x)
->

	i = heapsum(store(emptyheap, 3, 3), store(emptyheap, 2, 7))
->
	select(i, X) = X & X != 0




/*	\forall int h1, h2; (
		disjoint(h1, h2) ->
		\forall int x; (select(heapsum(h1, h2), x) = select(h1, x) |
			        select(heapsum(h1, h2), x) = select(h2, x))
	)*/

//	\forall int h1, h2, h3; heapeq(heapsum(heapsum(h1, h2), h3),
//		    	      	       heapsum(h1, heapsum(h2, h3)))

//	\forall int h1, h2; heapeq(heapsum(h1, h2), heapsum(h2, h1))

//	\forall int h1, h2; (disjoint(h1, h2) <-> disjoint(h2, h1))
}