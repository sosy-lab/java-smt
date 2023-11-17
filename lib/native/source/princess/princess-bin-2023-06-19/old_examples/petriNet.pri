// Simple Petri net for a producer-consumer system

\existentialConstants {
  int S1, S2, S3, S4, S5;
}

\predicates {
  reach(int, int, int, int, int);
}

\problem {
  // Transitions of the Petri net
  \forall int s1, s2, s3, s4, s5;
  (reach(s1, s2, s3, s4, s5) -> s2 > 0 -> reach(s1+1, s2-1, s3, s4, s5))
->
  \forall int s1, s2, s3, s4, s5;
  (reach(s1, s2, s3, s4, s5) -> s1 > 0 -> reach(s1-1, s2+1, s3+1, s4, s5))
->
  \forall int s1, s2, s3, s4, s5;
  (reach(s1, s2, s3, s4, s5) -> s3 > 0 & s4 > 0 -> reach(s1, s2, s3-1, s4-1, s5+1))
->
  \forall int s1, s2, s3, s4, s5;
  (reach(s1, s2, s3, s4, s5) -> s5 > 0 -> reach(s1, s2, s3, s4+1, s5-1))
->
  reach(S1, S2, S3, S4, S5)
->
  S1 >= 0 & S2 >= 0 & S3 >= 0 & S4 >= 0 & S5 >= 0
  &
  reach(S1, S2, S3+1, S4, S5)
}