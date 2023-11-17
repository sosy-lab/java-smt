\predicates {
  next(int,int);
  previous(int,int);
}

\problem {
  next(0,1)
->
  previous(1,0)
->
  \forall int x, y; (next(x,y) -> previous(y,x))
&
  \forall int x, y; (previous(x,y) -> next(y,x))
}
