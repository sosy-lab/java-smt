\problem {
\forall int x, y; ((
////////////////////////////////////////////////////
// Optimisation example: Maximise f(x,y)=3x+2y subject
// to the following inequalities

		2*x + y <= 18 &
  		2*x + 3*y <= 42 &
  		3*x + y <= 24 &
  		x >= 0 & y >= 0

////////////////////////////////////////////////////
// State the maximality of the solution:
&
		\forall int x2, y2; (
			2*x2 + y2 <= 18 &
  			2*x2 + 3*y2 <= 42 &
  			3*x2 + y2 <= 24 &
  			x2 >= 0 & y2 >= 0
		->
			3*x + 2*y >= 3*x2 + 2*y2
		)
	)

////////////////////////////////////////////////////
// The only solution should be:
<->
	x = 3 & y = 12
////////////////////////////////////////////////////
)
}