\functions {
   int c;
}

\problem {
  // With proper formula simplification, the quantified
  // formula can immediately be replaced with true; the final
  // countermodel won't mention c

  \exists int x; (c >= 10*x + 3 & c <= 10*x + 12)
->
  false
}