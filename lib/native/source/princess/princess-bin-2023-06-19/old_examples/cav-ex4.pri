/**
 Example taken from
 "Complete instantiation for quantified SMT formulas"
 Yeting Ge and Leonardo de Moura
 */

\functions {
  int f(int);
  int h(int);
  int h'(int);
  int a, b, c, n, i, j;
}

\predicates {
  p(int, int);
}

\problem {
  \forall int x1, x2; {f(x1), f(x2)} (0<=x1 -> x1<=x2 -> x2<=n -> h(f(x1)) <= h(f(x2)))
->
  \forall int x1; {f(x1)} (0<=x1 -> x1<=n -> f(x1)!=a)
->
  \forall int x1; {h'(x1)} (x1!=a -> h'(x1)=h(x1))
->
  h'(a)=b
->
  0<=i -> i <= j -> j <= n -> h'(f(i)) > h'(f(j))
->
  false
}