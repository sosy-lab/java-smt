/**
 Example taken from
 "Complete instantiation for quantified SMT formulas"
 Yeting Ge and Leonardo de Moura
 */

\functions {
  int f(int);
  int g(int, int);
  int h(int);
  int a, b;
}

\predicates {
  p(int, int);
}

\problem {
  \forall int x1, x2; (g(x1,x2)=0 | h(x2)=0)
->
  \forall int x1; g(f(x1), b)+1 <= f(x1)
->
  h(b) = 1
->
  f(a) = 0
->
  false
}