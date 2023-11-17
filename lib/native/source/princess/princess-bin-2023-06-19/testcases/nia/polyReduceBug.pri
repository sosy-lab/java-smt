
// Example that previous lead to an infinite loop in the Polynomial class

\functions {
  int P0, P1;
  int mul(int x, int y) { x * y };
}

\problem {

!(P1 = 0) & !((mul(2266521664 * mul(mul(292681 * P0, P0), P0), (292681 * mul(mul(158340421 * mul(24945510 * P0, P0), P0), P0) + -318)) + -541) >= 0)
 

-> false

}