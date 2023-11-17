/**
 * A simple riddle taken from
 * http://puzzleparasite.blogspot.de/2015/04/2014-slovak-puzzle-championships.html
 */

\functions {
  int H, A, T, E, L, O, V, S, K;
}

\problem {
  \min(H, A, T, E, L, O, V, S, K) = 1
&
  \max(H, A, T, E, L, O, V, S, K) = 9
&
  \distinct(H, A, T, E, L, O, V, S, K)

&
  H+A+T+E = 20
&
  L+O+V+E = 14
&
  S+O+L+V+E = 20
&
  A+S+K = 14
&
  L+E+A+S+T = 20
&
  V+E+T = 14

-> false
}
