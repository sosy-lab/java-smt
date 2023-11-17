\existentialConstants {
  int A;
}

\functions {
  \partial int gcd(int, int);
}

\predicates {
  divides(int, int);
}

\problem {
     \forall int x; divides(x, x)
  -> \forall int x, y; (divides(x, y) -> divides(x, y+x) & divides(x, y-x))
  -> \forall int x, y; (divides(x, y) & y < x & y > -x -> y = 0)
  -> \forall int x, y; {gcd(x, y)}
                       (divides(gcd(x, y), x) & divides(gcd(x, y), y) &
                        \forall int z; (divides(z, x) & divides(z, y) & z > 1 -> z <= gcd(x, y)))
  ->
  //   A = gcd(42, 49)
   gcd(12,18)<=gcd(42, 49)
}
