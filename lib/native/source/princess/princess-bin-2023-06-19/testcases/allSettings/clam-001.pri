/**
Examples taken from the paper
"A Framework for the Flexible Integration of a Class of
Decision Procedures into Theorem Provers",
Predrag Janicic, Alan Bundy, Ian Green
*/

\predicates {
	min(int, int);
	max(int, int);
}

\problem {
	\forall int x, a, b; (min(x, a) -> max(x, b) -> a <= b)
->
	\forall int l, a, k, min_a, max_a;
	(min(a, min_a) -> max(a, max_a) ->
	 l <= min_a & 0 < k -> l < max_a + k)
}