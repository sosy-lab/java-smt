\sorts {
  Col { red; green; blue; };
  BoolList { nil; cons(bool head, BoolList tail); };
}

\functions {
  Col c;
}

\problem {
  (is_green(c) | is_red(c) | is_blue(c))
&
  cons(is_green(c), cons(is_red(c), cons(is_blue(c), nil))) !=
  cons(false, cons(false, cons(false, nil)))
&
  (cons(is_green(c), cons(is_red(c), cons(is_blue(c), nil))) =
   cons(false, cons(true, cons(false, nil)))
   <->
   c = red)
}
