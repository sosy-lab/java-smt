
\functions {
  \partial int tree(int, int);
  \partial int leave(int);
  \partial int left(int);
  \partial int right(int);
  \partial int value(int);

  \partial int type(int);
  \partial int size(int);

  int a, b, c;
}

\problem {
  \forall int x, y; {tree(x, y)} left(tree(x, y)) = x
&
  \forall int x, y; {tree(x, y)} right(tree(x, y)) = y
&
  \forall int x; {leave(x)} value(leave(x)) = x
&
  \forall int x, y; {tree(x, y)} type(tree(x, y)) = 0
&
  \forall int x; {leave(x)} type(leave(x)) = 1
&
  \forall int x; {size(x)} size(x) > 0
&
  \forall int x; {leave(x)} size(leave(x)) = 1
&
  \forall int x, y; {tree(x, y)} size(tree(x, y)) = size(x) + size(y)
  
->

  \part[left]  (a = tree(b, leave(42)) & b = tree(leave(7), leave(8)) & c = right(a))
->
  \part[right]  (size(a) > 0 & value(right(a)) > value(right(left(a))) & value(c) > 0)

}

\interpolant{left; right}