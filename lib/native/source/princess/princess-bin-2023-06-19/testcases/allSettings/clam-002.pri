/**
Examples taken from the paper
"A Framework for the Flexible Integration of a Class of
Decision Procedures into Theorem Provers",
Predrag Janicic, Alan Bundy, Ian Green
*/

\functions {
	int maxint;
}

\predicates {
	delta(int, int, int, int);
}

\problem {
	\forall int x, y, z, d; (delta(x, y, z, d) -> d <= y)
->
	\forall int lp, lt, i, pat, c, d;
	(delta(pat, lp, c, d) -> lp + lt <= maxint & i <= lt -> i + d <= maxint)
}