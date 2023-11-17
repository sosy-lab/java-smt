

\functions{
  int[0, 65535] a, b;
  int x;
}

\problem {
  a * b >= 256^2 &
  x = 65535 / a &
//  x * a <= 65535 & x * a > 65535 - a &
  x >= b // & (x - b) * a >= 0

-> false
}