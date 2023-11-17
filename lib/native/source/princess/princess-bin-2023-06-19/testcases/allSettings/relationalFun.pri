\functions {
  \partial int f(int);
  \relational int g(int);
  \partial \relational int h(int);
}

\problem {
  \forall int x, y1, y2; (f(x) = y1 -> f(x) = y2 -> y1 = y2)
&
  \forall int x, y1, y2; (f(x) = f(x))
&
  (
    \forall int x, y; {g(x)} (g(x)=y -> false)
  ->
    false
  )
}