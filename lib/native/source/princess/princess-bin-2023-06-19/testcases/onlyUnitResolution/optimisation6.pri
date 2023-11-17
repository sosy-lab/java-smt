\existentialConstants {
	int w;
	int x,y;
}

\predicates {
	p(int, int);
}

\problem {
	\forall int x, y; (
		2*x + y <= 18 &
  		2*x + 3*y <= 42 &
  		3*x + y <= 24 &
  		x >= 0 & y >= 0
	->
		p(x,y)
	)
->
	\forall int x, y; (
		p(x,y)
	->
		2*x + y <= 18
	)
->
	\forall int x, y; (
		p(x,y)
	->
  		2*x + 3*y <= 42
	)
->
	\forall int x, y; (
		p(x,y)
	->
  		3*x + y <= 24
	)
->
	\forall int x, y; (
		p(x,y)
	->
  		x >= 0
	)
->
	\forall int x, y; (
		p(x,y)
	->
  		y >= 0
	)
->
	(
		p(x,y) &
		\forall int x2, y2; (p(x2, y2) ->
				     3*x + 2*y >= 3*x2 + 2*y2)
	)
//	\forall int x, y; (
//		p(x,y) -> 3*x + 2*y != w
//	)
}