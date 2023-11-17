%------------------------------------------------------------------------------
% File     : ARI616=1 : TPTP v5.3.0. Released v5.1.0.
% Domain   : Arithmetic
% Problem  : If intervals intersect, then sum_of_radii >= distance_of_centers
% Version  : Especial.
% English  :

% Refs     : [Wal10] Waldmann (2010), Email to Geoff Sutcliffe
% Source   : [Wal10]
% Names    :

% Status   : Theorem
% Rating   : 0.50 v5.3.0, 0.57 v5.2.0, 0.60 v5.1.0
% Syntax   : Number of formulae    :    2 (   0 unit;   1 type)
%            Number of atoms       :   10 (   0 equality)
%            Maximal formula depth :    9 (   7 average)
%            Number of connectives :    5 (   0   ~;   0   |;   2   &)
%                                         (   1 <=>;   2  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    3 (   1   >;   2   *;   0   +;   0  <<)
%            Number of predicates  :    5 (   3 propositional; 0-3 arity)
%            Number of functors    :    2 (   0 constant; 1-2 arity)
%            Number of variables   :    8 (   0 sgn;   7   !;   1   ?)
%            Maximal term depth    :    3 (   1 average)
%            Arithmetic symbols    :    4 (   2 pred;    2 func;    0 numbers)
% SPC      : TFF_THM_NEQ_ARI

% Comments :
%------------------------------------------------------------------------------
tff(p_type,type,(
    p: ( $int * $int * $int ) > $o )).

tff(sum_of_radii_gt_distance_of_centers,conjecture,
    ( ! [X: $int,Y: $int,Z: $int] :
        ( ( $lesseq($sum(Y,$uminus(Z)),X)
          & $lesseq(X,$sum(Y,Z)) )
      <=> p(X,Y,Z) )
   => ! [Y1: $int,Z1: $int,Y2: $int,Z2: $int] :
        ( ? [X: $int] :
            ( p(X,Y1,Z1)
            & p(X,Y2,Z2) )
       => $lesseq($sum(Y1,$uminus(Y2)),$sum(Z1,Z2)) ) )).

%------------------------------------------------------------------------------
