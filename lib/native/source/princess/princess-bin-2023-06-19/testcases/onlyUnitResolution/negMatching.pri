\predicates {
  p(int);
  // match on negative occurrences of q in quantified formulae
  \negMatch q(int);
}

\problem {
  p(0) & !q(1)
->
  \forall int x, y; (p(x) -> q(y) | p(x+y))
->
  p(100)
}
