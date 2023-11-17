\functions {
int x1;
int x2;
int sum;
}

\problem {
  \part[part00000] ( x1 >= -4 & x1 <= 0 )
     ->
  \part[part00001] ( x2 < 4 &
                     \exists int sum_div; 8 * sum_div + x2 = 1 + x1 )
     ->
  \part[part00002] true
     ->
  \part[part00003] x2 >= 2
     ->
  \part[part00004] false
}
\interpolant{part00000;part00001,part00002,part00003,part00004}
