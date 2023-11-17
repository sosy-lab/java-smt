\functions {
  int f(int);
}

\problem {
// The following holds even without requiring that f is surjective,
// because the equation "f(\eps int y; x = f(y)) = x" is internally
// rewritten to
//       \forall int y; (x = f(y) -> f(y) = x)

  \forall int x; f(\eps int y; x = f(y)) = x
}