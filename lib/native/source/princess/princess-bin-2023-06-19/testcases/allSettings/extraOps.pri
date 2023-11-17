/**
 * Additional pre-defined operators
 * /, % are Euclidian division and modulus
 */

\predicates {
  p; q;
}

\functions {
  int x;
}

\problem {
  x = x / 5 * 5 + x % 5 &
  x % 5 >= 0 &
  x % 5 < 5
&
  x = x / (-5) * (-5) + x % (-5) &
  x % (-5) >= 0 &
  x % (-5) < 5
&
  \abs(x) >= x
&
  \abs(x)^2 = x^2
&
  (x >= 0 -> \max(x / 5, x) = x)
&
  (x >= 0 -> \min(x / 5, x) = x / 5)
&
  (x < 0 <-> \distinct(x, \abs(x)))
&
  ((p <-> q) <-> (p -> q) & (p <- q))
}
