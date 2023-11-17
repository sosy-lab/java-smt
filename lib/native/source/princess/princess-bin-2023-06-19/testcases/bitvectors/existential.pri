\existentialConstants {
  bool b0, b1, b2, b3, b4, b5, b6, b7, b8, b9;
}

\problem {
  \exists bv[64] x0, x1, x2, x3, x4, x5, x6, x7, x8, x9; (
    b0 = (x0 % 3 = 0) &
    b1 = (x1 % 3 = 0) &
    b2 = (x2 % 3 = 0) &
    b3 = (x3 % 3 = 0) &
    b4 = (x4 % 3 = 0) &
    b5 = (x5 % 3 = 0) &
    b6 = (x6 % 3 = 0) &
    b7 = (x7 % 3 = 0) &
    b8 = (x8 % 3 = 0) &
    b9 = (x9 % 3 = 0) &
    x1 = x0 + 1 &
    x2 = x1 + 2 &
    x3 = x2 + 3 &
    x4 = x3 + 4 &
    x5 = x4 + 5 &
    x6 = x5 + 6 &
    x7 = x6 + 7 &
    x8 = x7 + 8 &
    x9 = x8 + 9
  )
}

