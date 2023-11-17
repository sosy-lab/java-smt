\sorts {
  /* Declare sorts and algebraic data-types */
  Dec { null; dig(int[0, 9] val, Dec prefix); };
}

\functions {
  \partial nat value(Dec d);
  Dec d1;
}

\problem {
  \forall Dec c;
    {value(c)} ((c.is_null & value(c) = 0) |
                (c.is_dig & (value(c) = c.val + 10*value(c.prefix))))

->

  value(d1) = 20

-> false
}

