
\functions {
  int a, b;
}

\predicates {
  less(int x, int y) { x < y };
  inRange(int x) { 0 <= x & x < l };
}

\functions {
  int l;
}

\problem {
  (less(a, b) <-> a < b)
&
  (inRange(a) & inRange(b) & \distinct(a, b) -> l >= 2)
}