\functions {
  \partial int f(int);
  \partial int g(int);
}

\predicates {
  p(int, int);
}

\problem {
   \forall int x; \forall int y; (p(x, f(y)) | p(x, g(y)))
->
   \exists int z; (
     (p(z, f(f(z))) | p(z, g(f(z))))
     &
     (p(z, f(g(z))) | p(z, g(g(z))))     
   )
}