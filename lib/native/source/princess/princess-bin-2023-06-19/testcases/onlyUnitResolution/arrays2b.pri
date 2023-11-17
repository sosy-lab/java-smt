
\predicates {
  range(int);
}

\functions {
  int select(int, int);
  int store(int, int, int);
  int ar;
  int p0;
  int p1;
  int p2;
  int p3;
  int p4;
  int p5;
  int p6;
  int p7;
  int p8;
  int p9;
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
    \forall int x; (range(x) -> x=p0 | x=p1 | x=p2 | x=p3 | x=p4
                              | x=p5 | x=p6 | x=p7 | x=p8 | x=p9)
->
    select(ar, p0) = 0
->
    select(ar, p1) = 1
->
    select(ar, p2) = 2
->
    select(ar, p3) = 3
->
    select(ar, p4) = 4
->
    select(ar, p5) = 5
->
    select(ar, p6) = 6
->
    select(ar, p7) = 7
->
    select(ar, p8) = 8
->
    select(ar, p9) = 9
->

    \forall int x; (range(x) -> select(ar, x) >= 0)
}