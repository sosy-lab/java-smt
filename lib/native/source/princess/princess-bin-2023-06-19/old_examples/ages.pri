\existentialConstants {
  int my_years;
}

\problem {
\exists int grandson_years, son_years,
            grandson_months, son_weeks,
            grandson_days; (

  grandson_days = grandson_months * 4 * 7
&
  grandson_months = grandson_years * 12
&
  son_weeks = son_years * 12 * 4
&
  grandson_days = son_weeks
&
  grandson_months = my_years
&
  grandson_years + son_years + my_years = 140
)
}