\functions {
  int x1, x2, x3, x4;
}

\problem {
  x1 != x2 & x1 != x3 & x1 != x4 &
  x2 != x3 & x2 != x4 &
  x3 != x4 &
  x1 >= 0 & x2 >= 0 & x3 >= 0 & x4 >= 0 &
  x1 <= 2 & x2 <= 2 & x3 <= 2 & x4 <= 2
->
  false
}