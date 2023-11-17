\sorts {
  Colour { red; green; blue; };
  ColourList { nil; cons(Colour col, ColourList next); };
}

\problem {
  red != green
&
  cons(red, nil) != cons(blue, nil)
}
