/**
 * Case that previously led to an exception, because of shifting with a
 * potentially negative argument.
 */

\functions {
  signed bv[32] iX;
  int log(signed bv[32] y) {
    \eps int x; ( (1.\as[signed bv[34]] << x) <= y.\as[signed bv[34]] &
                  (1.\as[signed bv[34]] << (x + 1)) > y.\as[signed bv[34]] )
  };
}

\problem {
  iX = log(2147483647.\as[signed bv[32]])

-> false

}
