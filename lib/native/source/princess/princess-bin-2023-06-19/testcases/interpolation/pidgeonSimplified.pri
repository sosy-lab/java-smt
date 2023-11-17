\functions {
  int x1, x2, x3, x4;
}

\problem {
\part[right](x1 != x2 & x1 != x3) &
\part[left]( x2 != x3 &
  x1 >= 0 & x2 >= 0 & x3 >= 0 &
  x1 <= 1 & x2 <= 1 & x3 <= 1 )
->
  false
}

\interpolant{left; right}
