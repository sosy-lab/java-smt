\predicates {
	p(int, int);
}

\problem {
	\forall int x, y; (
		p(x,y)
	<->
		2*x + y <= 18 &
  		2*x + 3*y <= 42 &
  		3*x + y <= 24 &
  		x >= 0 & y >= 0
	)
->
	\exists int x, y; p(x,y)
}