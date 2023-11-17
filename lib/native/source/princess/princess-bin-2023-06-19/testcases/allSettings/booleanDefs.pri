
\functions {
  int a, b, c;
}

\predicates {
  p; q; r;
}

\problem {
  (p <-> a >= 0)
->
  (!q <-> (a = b + 1 & c < 0))
->
  (q & !p <-> r)

->
  a != 13
}