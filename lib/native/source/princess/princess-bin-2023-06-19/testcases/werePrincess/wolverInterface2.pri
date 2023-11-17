\functions {
  int x, y, z;
  int ar;
}

\problem {
  \part[p0] (select(ar, x) = 1)
->
  \part[p1] (select(ar, y) >= select(ar, x))
->
  \part[p2] (z = select(ar, y)+1)
->
  \part[p3] (z < 0)
->
  false
}
