/**
 * Case that previously led to a wrong model (Y = 0)
 */

\functions {
  int Y;
}

\problem {
  ((1.\as[signed bv[34]] << Y) <= 100.\as[signed bv[34]] &
                  (1.\as[signed bv[34]] << (Y + 1)) > 100.\as[signed bv[34]] )

-> false

}
