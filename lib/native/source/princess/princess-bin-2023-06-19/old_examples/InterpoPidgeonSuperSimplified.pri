\functions {
  int x1, x2, x3, x4;
}

\problem {
\part[right](x1 != x2) &
\part[left](
  x1 >= 0 & x2 >= 0 &
  x1 <= 0 & x2 <= 0)
->
  false
}

\interpolant{left; right}
