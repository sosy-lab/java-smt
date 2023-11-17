\existentialConstants {
  int x0, x1;
}

\predicates {
  notSet(int,int);
}

\problem {
  \forall int x0, x1, y0, y1; (!notSet(x0,x1) ->
                               !notSet(y0,y1) -> !notSet(x0+y0, x1+y1))
->
  \forall int x0, x1; (x0 >= 20 & x1 >= 10 & x1 <= 15 -> !notSet(x0,x1))
->
  !notSet(x0,x1) & x1 > 30
}

