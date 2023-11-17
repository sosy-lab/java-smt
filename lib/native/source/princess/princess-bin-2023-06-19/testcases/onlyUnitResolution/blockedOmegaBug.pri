/**
 * Situation that led to an assertion failure in OmegaTask,
 * due to incorrect handling of BlockedFormulaTask
 */

\functions {
  \partial int f(int);
  int a, b, c, d;
}

\problem {
  f(a) = c
->
  f(b) = d
->
  false
}
