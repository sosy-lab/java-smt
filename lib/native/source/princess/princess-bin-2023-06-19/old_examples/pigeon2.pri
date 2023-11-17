\functions {
  int f(int);
  int x1, x2, x3, x4;
}

\problem {
/*  This causes problems with +posUnitResolution:
  \forall int x; {f(x)} \exists int y; f(y) > f(x)
->
*/
  x1 >= 0 & x2 >= 0 & x3 >= 0 & x4 >= 0 &
  x1 <= 2 & x2 <= 2 & x3 <= 2 & x4 <= 2 &
  f(x1) < f(x2) & f(x2) < f(x3) & f(x3) < f(x4)
->
  false
}