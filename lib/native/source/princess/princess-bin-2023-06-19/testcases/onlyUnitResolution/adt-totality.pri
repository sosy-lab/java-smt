\sorts {
  C { red; green; };
}

\functions {
  C x;
  C f(C);
}

\problem {
  \forall C x; f(x) != x
->
  \exists C x; f(x) = green
}
