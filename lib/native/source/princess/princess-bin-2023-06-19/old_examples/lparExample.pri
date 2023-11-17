/**
 * Example used in the LPAR 2008 paper
 * "A Constraint Sequent Calculus for First-Order Logic
 *  with Linear Integer Arithmetic"
 */

\predicates {
  p(int);
}

\problem {
  \forall int x; p(2*x)
->
  \forall int x; !p(2*x+1)
->
  \forall int x; (p(x) -> p(x+10))
}
