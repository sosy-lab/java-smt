/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

/**
 * Background predicate for the Princess-Wolverine interface
 */

\predicates {
  inArray(int);
  inSigned(int, int);
  inUnsigned(int, int);
}

\functions {
  \partial int select(int, int);
  \partial int store(int, int, int);

// Predicate for array equality, to implement extensionality. Because
// we want to match both on positive and negative occurrences of the
// predicate, we declare it as a function and encode positive
// occurrences as eqArrays(int, int) = 0, negative occurrences as
// eqArrays(int, int) != 0
  \partial \relational int eqArrays(int, int);

  \partial \relational int shiftLeft(int, int);
  \partial \relational int shiftRight(int, int);

  \relational \partial int addSigned(int, int, int);
  \relational \partial int addUnsigned(int, int, int);

  \relational \partial int mulSigned(int, int, int);
  \relational \partial int mulUnsigned(int, int, int);

  \relational \partial int divSigned(int, int, int);
  \relational \partial int divUnsigned(int, int, int);

  \relational \partial int subSigned(int, int, int);
  \relational \partial int subUnsigned(int, int, int);
  
  \relational \partial int minusSigned(int, int);
  \relational \partial int minusUnsigned(int, int);
  
// Bit-wise boolean operations that are independent of
// the number of bits
  \partial \relational int and(int, int);

// Modulo, which we assume not reveal any overflows (correct?)
  \partial \relational int modulo(int, int);

// General (unbounded) multiplication
  \partial \relational int mul(int, int);

// General (unbounded) division
  \partial \relational int div(int, int);

// Absolute value
  \partial \relational int abs(int);

// Arith-1 functions  
  \partial \relational int equals(int, int);
  \partial \relational int lessThan(int, int);
  \partial \relational int lessEqual(int, int);
  \partial \relational int bitNegU1(int);

// Typecasts
  \relational \partial int signed2unsigned(int, int);

// Pairs
  \partial int pair(int, int);
  \partial int proj1(int);
  \partial int proj2(int);

}

\problem {

////////////////////////////////////////////////////////////////////////////////
// Array axioms

  \forall int ar, ind, val;
     {store(ar, ind, val)}
//     {select(store(ar, ind, val), ind)}  // this might be chosen for more efficiency
                                           // (but is incomplete)
     select(store(ar, ind, val), ind) = val
->
  \forall int ar, ind1, ind2, val;
     {select(store(ar, ind1, val), ind2)}
     (ind1 != ind2 ->
      select(store(ar, ind1, val), ind2) = select(ar, ind2))
->
  \forall int ar1, ar2; {eqArrays(ar1, ar2)}
    (eqArrays(ar1, ar2) != 0 ->
     \exists int x; select(ar1, x) != select(ar2, x))
->
  \forall int ar1, ar2, x; {eqArrays(ar1, ar2), select(ar1, x)}
//                           {eqArrays(ar1, ar2), select(ar2, x)}  // seems enough to
                                                                   // have one trigger
    (eqArrays(ar1, ar2) = 0 -> select(ar1, x) = select(ar2, x))
->

////////////////////////////////////////////////////////////////////////////////
// Bit-shifts (which are used in most of the other definitions)

  \forall int x, y; {shiftLeft(x, y)} (
    y > 32 -> shiftLeft(x, y) = shiftLeft(4*1024*1024*1024*x, y-32))
&
  \forall int x; {shiftLeft(x, 32)}
    shiftLeft(x, 32) = 4*1024*1024*1024*x
&
  \forall int x; {shiftLeft(x, 31)}
    shiftLeft(x, 31) = 2*1024*1024*1024*x
&
  \forall int x, y; {shiftLeft(x, y)} (
    y < 31 & y >= 16 -> shiftLeft(x, y) = shiftLeft(64*1024*x, y-16))
&
  \forall int x, y; {shiftLeft(x, y)} (
    y < 16 & y > 8 -> shiftLeft(x, y) = shiftLeft(256*x, y-8))
&
  \forall int x, y; {shiftLeft(x, 8)}
    shiftLeft(x, 8) = 256*x
&
  \forall int x, y; {shiftLeft(x, y)} (
    y < 8 & y >= 4 -> shiftLeft(x, y) = shiftLeft(16*x, y-4))
&
  \forall int x, y; {shiftLeft(x, y)} (
    y < 4 & y >= 2 -> shiftLeft(x, y) = shiftLeft(4*x, y-2))
&
  \forall int x, y; {shiftLeft(x, 1)}
    shiftLeft(x, 1) = 2*x
&
  \forall int x; {shiftLeft(x, 0)}
    shiftLeft(x, 0) = x
&

  \forall int x, y, res; {shiftRight(x, y)} (
    shiftRight(x, y) = res ->
    \exists int subres, diff; (
      subres = shiftLeft(res, y) & diff = shiftLeft(1, y) & (
      x >= 0 & subres <= x & subres + diff > x
      |
      x < 0 & subres >= x & subres - diff < x
    )))
&

////////////////////////////////////////////////////////////////////////////////
// Domain predicates

  \forall int x, base; (inSigned(base, x) -> x >= -base & x < base)
&
  \forall int x, base; (inUnsigned(base, x) -> x >= 0 & x < 2*base)
&


////////////////////////////////////////////////////////////////////////////////
// Addition with overflow

  \forall int x, y, res, base; {addSigned(base, x, y)} (
    addSigned(base, x, y) = res ->
    (x + y >= base -> res = x + y - 2*base) &
    (x + y < -base -> res = x + y + 2*base) &
    (x + y >= -base & x + y < base -> res = x + y)
  )

/* This version currently does not perform well due to rounding
  \forall int x, y, res, width; {addSigned(width, x, y)} (
    addSigned(width, x, y) = res ->
    \exists int k; res = x + y + shiftLeft(k, width) &
    inSigned(width, res)
  ) */

&

  \forall int x, y, res, base; {addUnsigned(base, x, y)} (
    addUnsigned(base, x, y) = res ->
    (x + y >= 2*base -> res = x + y - 2*base) &
    (x + y < 2*base -> res = x + y)
  )

////////////////////////////////////////////////////////////////////////////////
// Unary minus with overflow

&
  \forall int base, x, res; {minusSigned(base, x)} (
    minusSigned(base, x) = res ->
    (-x >= base -> res = -x - 2*base) &
    (-x < base -> res = -x)
  )

&
  \forall int base, x, res; {minusUnsigned(base, x)} (
    minusUnsigned(base, x) = res ->
    (x = 0 -> res = 0) &
    (x > 0 -> res = 2*base -x)
  )

////////////////////////////////////////////////////////////////////////////////
// Subtraction with overflow

&
  \forall int base, x, y; {subSigned(base, x, y)}
    subSigned(base, x, y) = addSigned(base, x, minusSigned(base, y))
&
  \forall int base, x, y; {subUnsigned(base, x, y)}
    subUnsigned(base, x, y) = addUnsigned(base, x, minusUnsigned(base, y))

////////////////////////////////////////////////////////////////////////////////
// Bit-wise and. This mainly does a case analysis over the second
// argument, which means that it is usually more
// efficient to have constant values as the second argument

&
  \forall int x; {and(x, 0)} and(x, 0) = 0
&
  \forall int x; {and(x, -1)} and(x, -1) = x
&
  \forall int x, y, res; {and(x, y)}
      ((y >= 1 | y <= -2) -> and(x, y) = res ->
       \exists int k, l, m, n, subres; (
           and(k, l) = subres &
           x = 2*k + m & y = 2*l + n & m >= 0 & m <= 1 & (
             n = 0 & res = subres * 2
             |
             n = 1 & res = subres * 2 + m
       )))
&

////////////////////////////////////////////////////////////////////////////////
// Modulo

  \forall int x, y, res; {modulo(x, y)}
      (modulo(x, y) = res & y != 0 ->
       \exists int k; mul(k, y) + res = x &
       0 <= res & (res < y | res < -y))
&

////////////////////////////////////////////////////////////////////////////////
// General multiplication (on the unbounded integers)

  \forall int x; {mul(x, 0)} mul(x, 0) = 0
&
  \forall int x; {mul(x, -1)} mul(x, -1) = -x
&
  \forall int x, y, res; {mul(x, y)}
      ((y >= 1 | y <= -2) -> mul(x, y) = res ->
       \exists int l, n, subres; (
           mul(2*x, l) = subres &
           y = 2*l + n & (
             n = 0 & res = subres
             |
             n = 1 & res = subres + x
       )))
&

  \forall int base, x; {mulUnsigned(base, x, 0)} mulUnsigned(base, x, 0) = 0
&
  \forall int base, x, y, res; {mulUnsigned(base, x, y)}
      (y >= 1 -> mulUnsigned(base, x, y) = res ->
       \exists int l, n, subres; (
           mulUnsigned(base, addUnsigned(base, x, x), l) = subres &
           y = 2*l + n & (
             n = 0 & res = subres
             |
                // HACK to prevent the "addUnsigned" from escaping
                // (should be fixed in the function encoder, TODO)
             n = 1 & \exists int x'; (x' = x & res = addUnsigned(base, subres, x'))
       )))
&

  \forall int base, x; {mulSigned(base, x, 0)} mulSigned(base, x, 0) = 0
&
  \forall int base, x; {mulSigned(base, x, -1)} mulSigned(base, x, -1) = minusSigned(base, x)
&
  \forall int base, x, y, res; {mulSigned(base, x, y)}
      ((y >= 1 | y <= -2) -> mulSigned(base, x, y) = res ->
       \exists int l, n, subres; (
           mulSigned(base, addSigned(base, x, x), l) = subres &
           y = 2*l + n & (
             n = 0 & res = subres
             |
                // HACK to prevent the "addSigned" from escaping
                // (should be fixed in the function encoder, TODO)
             n = 1 & \exists int x'; (x' = x & res = addSigned(base, subres, x'))
       )))
&

/*
 * The following axioms do not perform well due to rounding

  \forall int x, y, res, width; {mulUnsigned(width, x, y)} (
    mulUnsigned(width, x, y) = res ->
    \exists int k; res = mul(x, y) + shiftLeft(k, width) &
    inUnsigned(width, res)
  )
&
  \forall int x, y, res, width; {mulSigned(width, x, y)} (
    mulSigned(width, x, y) = res ->
    \exists int k; res = mul(x, y) + shiftLeft(k, width) &
    inSigned(width, res)
  )
&
*/

////////////////////////////////////////////////////////////////////////////////
// General division (on the unbounded integers)

  \forall int x, y, res; {div(x, y)} (
      y != 0 ->
      \exists int mulres; (
         mul(div(x, y), y) = mulres &
         mulres <= x & (mulres > x + y | mulres > x - y)
      )
  )
&
  \forall int x, y, res, base; {divUnsigned(base, x, y)} (
    divUnsigned(base, x, y) = div(x, y)
  )
&
  \forall int x, y, res, base; {divSigned(base, x, y)} (
    divSigned(base, x, y) = res ->
    \exists int divres; (divres = div(x, y) &
                         (divres >= base -> res = divres - 2*base) &
                         (divres < base -> res = divres))
  )
&

////////////////////////////////////////////////////////////////////////////////
// Absolute value

  \forall int x; {abs(x)} (x >= 0 -> abs(x) = x)
&
  \forall int x; {abs(x)} (x <  0 -> abs(x) = -x)
&

////////////////////////////////////////////////////////////////////////////////
// Arith-1 Functions
// Equals

  \forall int x, y; {equals(x, y)} (x = y -> equals(x, y) = 1)
&
  \forall int x, y; {equals(x, y)} (x != y -> equals(x, y) = 0)
&

// LessEqual

  \forall int x, y; {lessEqual(x, y)} (x <= y -> lessEqual(x, y) = 1)
&
  \forall int x, y; {lessEqual(x, y)} (x > y -> lessEqual(x, y) = 0)
&

// LessThan

  \forall int x, y; {lessThan(x, y)} (x < y -> lessThan(x, y) = 1)
&
  \forall int x, y; {lessThan(x, y)} (x >= y -> lessThan(x, y) = 0)
&

// BitNegU1

  \forall int x; {bitNegU1(x)} (x = 0 -> bitNegU1(x) = 1)
&
  \forall int x; {bitNegU1(x)} (x != 0 -> bitNegU1(x) = 0)
&

////////////////////////////////////////////////////////////////////////////////
// Typecasts
// Signed to Unsigned

  \forall int base, x; {signed2unsigned(base, x)} (
    x < 0 -> signed2unsigned(base, x) = x + 2*base)
&
  \forall int base, x; {signed2unsigned(base, x)} (
    x >= 0 -> signed2unsigned(base, x) = x)
&

////////////////////////////////////////////////////////////////////////////////
// Pairs

  \forall int x, y; {pair(x, y)} (proj1(pair(x, y)) = x)
&
  \forall int x, y; {pair(x, y)} (proj2(pair(x, y)) = y)
&
  \forall int x, y; {proj1(x), proj2(x)} (pair(proj1(x), proj2(x)) = x)

////////////////////////////////////////////////////////////////////////////////
// Everything is negated (the definitions are premisses)

-> false
}
