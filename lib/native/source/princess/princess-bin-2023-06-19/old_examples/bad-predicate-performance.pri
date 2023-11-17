/**
 Remove the flag "\partial" in the function declarations
 to speed up this example
 */

\functions {
  \partial int f(int, int);
  \partial int g(int);
  \partial int h(int);
}

\predicates {
  p(int, int);
}

\problem {
  \forall int x; p(f(x, g(x)), f(g(x), x))
->
  \forall int y, z; !p(f(h(y), z), f(z, h(y)))
->
  false
}
