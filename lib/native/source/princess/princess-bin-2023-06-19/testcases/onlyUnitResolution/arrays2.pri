
\predicates {
  select(int, int, int);
  store(int, int, int, int);
  range(int);
}

\functions {
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
    \forall int x; (range(x) -> x=p0 | x=p1 | x=p2 | x=p3 | x=p4
                              | x=p5 | x=p6 | x=p7 | x=p8 | x=p9)
->
    select(ar, p0, 0)
->
    select(ar, p1, 1)
->
    select(ar, p2, 2)
->
    select(ar, p3, 3)
->
    select(ar, p4, 4)
->
    select(ar, p5, 5)
->
    select(ar, p6, 6)
->
    select(ar, p7, 7)
->
    select(ar, p8, 8)
->
    select(ar, p9, 9)
->

    \forall int x, y; (range(x) -> select(ar, x, y) -> y >= 0)
}