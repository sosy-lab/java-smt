\functions {
  int f(int);
  int x, z;
}

\problem {
  \forall int x1, x2; (f(x1) = f(x2) -> x1 = x2)
->

// This is only well-defined because f is injective
  (\eps int y; x = f(y)) = z  ->
  (\eps int y; x = f(y)) = z
}
