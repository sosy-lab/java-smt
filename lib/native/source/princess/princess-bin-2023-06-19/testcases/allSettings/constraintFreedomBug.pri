\existentialConstants {
	   int a, b, c, d;
}

\problem {
//	 \exists int y;
//	  ! (y + -1*d != 0 & a + -1*b >= 0 & -1*c + b + -2 >= 0)
//&
	 \exists int x;
	 (! (x = 0 & a + -1*b >= 0 & -1*c + b + -2 >= 0) &
	  ! (-1*x + c >= 0 & a + -1*b >= 0 & -1*c + b + -2 >= 0) &
	  ! (x + -1*b >= 0 & a + -1*b >= 0 & -1*c + b + -2 >= 0))
-> false
}