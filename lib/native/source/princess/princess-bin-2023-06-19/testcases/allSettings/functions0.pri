

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
	\forall int x, y; (f(x, y) -> x = y)
->
	\forall int x, y, z; (f(x, y) -> f(y, z) -> x = z)
}