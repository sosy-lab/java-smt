/**
 Example taken from
 "Complete instantiation for quantified SMT formulas"
 Yeting Ge and Leonardo de Moura
 */

\functions {
  \partial int f(int);
  \partial int h(int);
  \partial int h'(int);
  int a, b, c, n, i, j;
}

\predicates {
  p(int, int);
}

\problem {
  \part[p0] \forall int x1, x2; {f(x1), f(x2)} (0<=x1 -> x1<=x2 -> x2<=n -> h(f(x1)) <= h(f(x2)))
->
  \part[p1] \forall int x1; {f(x1)} (0<=x1 -> x1<=n -> f(x1)!=a)
->
  \part[p2] \forall int x1; {h'(x1)} (x1!=a -> h'(x1)=h(x1))
->
  \part[p3] h'(a)=b
->
  \part[p4] (0<=i -> i <= j -> j <= n -> h'(f(i)) > h'(f(j))
->
  false)
}

\interpolant{p0,p1,p2,p3;p4}
\interpolant{p4;p0,p1,p2,p3}