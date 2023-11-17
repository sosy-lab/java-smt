\functions {
  int a, b;
}

\predicates {
  A(int); B(int,int);
}

\problem {
  \forall int x; \forall int y; ( A(y) | x >= a | x <= b | x=0 & B(x,y) )
->
  \forall int x; \forall int y; ( A(y) | x >= a | x <= b )
}
