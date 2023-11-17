\functions {
  int x, y, z;
}

\problem {
  \part[p0] (x <= -5 | x >= 0 & x <= 5)
->
  \part[p1] (x-y <= 2 & x-y >= -2)
->
  \part[p2] (z = addSigned(2*1024*1024*1024, y, 13))
->
  \part[p3] (z > 20)
->
  // without the following assumptions, the problem becomes unprovable
  inSigned(2*1024*1024*1024, y) & inSigned(2*1024*1024*1024, x)
->
  false
}
