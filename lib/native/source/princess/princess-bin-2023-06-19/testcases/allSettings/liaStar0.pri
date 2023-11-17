\existentialConstants {
  int x0, x1;
}

\predicates {
  set(int,int);
}

\problem {
  \forall int x0, x1, y0, y1; (set(x0,x1) -> set(y0,y1) -> set(x0+y0, x1+y1))
->
  \forall int x0, x1; (x0 >= 20 & x1 >= 10 & x1 <= 15 -> set(x0,x1))
->
  set(x0,x1) & x1 > 30
}

