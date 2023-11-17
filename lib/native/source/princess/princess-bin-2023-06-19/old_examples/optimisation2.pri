/**
 Can be solved quickly with the option "-clausifier=simple"
 */

\predicates {
	p(int, int);
}

\problem {
	\forall int x, y; (
		(2*x + y <= 18 &
  		2*x + 3*y <= 42 &
  		3*x + y <= 24 &
  		x >= 0 & y >= 0)
	<->
		p(x,y)
	)
->
	\exists int x, y; (
		p(x,y) &
		\forall int x2, y2; (p(x2, y2) ->
				     3*x + 2*y >= 3*x2 + 2*y2)
	)
}
