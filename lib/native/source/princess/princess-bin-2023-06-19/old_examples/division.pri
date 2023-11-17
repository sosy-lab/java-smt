\existentialConstants {
  int A;
}

\predicates {
  divides(int, int);
}

\problem {
  \forall int x; divides(x, x)
->
  \forall int x, y; (divides(x, y) -> divides(x, y+x) & divides(x, y-x))
->
  \forall int x, y; (divides(x, y) & y < x & y > -x -> y = 0)
->
  divides(A, 42) & divides(A, 49)
  &
  \forall int x; (divides(x, 42) & divides(x, 49) & x > 1 -> x <= A)
}