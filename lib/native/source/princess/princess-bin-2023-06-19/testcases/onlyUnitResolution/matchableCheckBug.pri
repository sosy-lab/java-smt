\predicates {
  p(int, int);
}

// Check that Princess correctly detects that 
// the following quantified axiom can be handled
// entirely using unit resolution

\problem {
  \forall int x, y; (p(x, x+y) -> x=y)
->
  p(1, 4)
->
  false
}