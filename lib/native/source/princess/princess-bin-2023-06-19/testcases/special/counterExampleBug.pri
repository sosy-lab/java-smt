\predicates {
  inSigned(int, int);
}

\functions {
  \partial \relational int shiftLeft(int, int);
  \relational \partial int addSigned(int, int, int);
}

\functions {
  int x, y, z;
}

\problem {
  \forall int x, y, res; {addSigned(32, x, y)} (
    addSigned(32, x, y) = res ->
    (res = x + y | res = x + y - 4*1024*1024*1024 |
                   res = x + y + 4*1024*1024*1024) &
    res >= -2*1024*1024*1024 & res < 2*1024*1024*1024
  )
->
  \part[p0] (x <= -5 | x >= 0 & x <= 5)
->
  \part[p1] (x-y <= 2 & x-y >= -2)
->
  \part[p2] (z = addSigned(32, y, 13))
->
  \part[p3] (z > 20)
->
  false
}
