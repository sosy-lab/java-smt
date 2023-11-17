\existentialConstants {
  int x0, x1;
}

\predicates {
  set(int,int);
}

\problem {
  set(0,0)
->
  \forall int x0, x1, y0, y1; (x0 >= 20 & x1 >= 10 & x1 <= 15
                                -> set(y0,y1) -> set(x0+y0,x1+y1))
->
  set(x0,x1) & x1 >= 20
}

