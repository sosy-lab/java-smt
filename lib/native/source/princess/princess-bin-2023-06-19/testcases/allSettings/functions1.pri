

\predicates {
	f(int, int);
}

\problem {
// Totality
	\forall int x; \exists int y; f(x, y)
->
// Functionality
	\forall int x, y1, y2; (f(x, y1) -> f(x, y2) -> y1 = y2)
->

// some arbitrary problem
	\forall int x1, y1, x2, y2; (f(x1, y1) -> f(x2, y2) ->
				     x1 <= x2 -> y1 <= y2)
->
	\forall int x, y1, y2; (f(x, y1) -> f(x+1, y2) -> y1 <= y2)
}