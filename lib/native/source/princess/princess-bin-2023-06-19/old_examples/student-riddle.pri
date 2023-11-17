/*
  A variant of the riddle PUZ018-1:

  Three students share an apartment. On only one day of the week are
  all three students at home. No student is at home on three consecutive
  days. No two students are off on the same day more than once a week.
  The first student is off on Sunday, Tuesday, and Thursday. The second
  student is off on Thursday and Saturday. The third student is off
  on Sunday.  Which day of the week are all three students at home?

  Use option +model to get an answer.
 */

\sorts {
  Student { A; B; C; };
}

\existentialConstants {
  int[1,7] Day;
}

\predicates {
  \negMatch atHome(Student, int[1,7]);
}

\problem {
  \exists int[1,7] homeDay; (
    atHome(A, homeDay) & atHome(B, homeDay) & atHome(C, homeDay) &
    \forall int[1,7] day2; (
      atHome(A, day2) & atHome(B, day2) & atHome(C, day2) -> homeDay = day2))
&
  \forall (Student s; int[1,5] day) (
    !atHome(s, day) | !atHome(s, day+1) | !atHome(s, day+2))
&
  \forall (Student s1, s2; int[1,7] day1, day2) (
    s1 != s2 & !atHome(s1, day1) & !atHome(s2, day1) &
               !atHome(s1, day2) & !atHome(s2, day2) ->
    day1 = day2)
&
  !atHome(A, 1) & !atHome(A, 3) & !atHome(A, 5)
&
  !atHome(B, 5) & !atHome(B, 7)
&
  !atHome(C, 1)

-> atHome(A, Day) & atHome(B, Day) & atHome(C, Day)
}
