\functions {
  \partial int f(int);
  \relational int g(int);
  \partial \relational int h(int);
}

\problem {
  \forall int x, y1, y2; (g(x) = y1 -> g(x) = y2 -> y1 = y2)
|
  \forall int x; (g(x) = g(x))
|
  (
    \forall int x, y; {f(x)} (f(x)=y -> false)
  ->
    false
  )
}