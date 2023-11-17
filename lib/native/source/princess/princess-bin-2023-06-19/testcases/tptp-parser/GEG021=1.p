%------------------------------------------------------------------------------
% File     : GEG021=1 : TPTP v5.1.0. Released v5.1.0.
% Domain   : Arithmetic
% Problem  : Estimate distance between cities (one step)
% Version  : Especial.
% English  :

% Refs     : [Wal10] Waldmann (2010), Email to Geoff Sutcliffe
% Source   : [Wal10]
% Names    :

% Status   : Theorem
% Rating   : 0.67 v5.1.0
% Syntax   : Number of formulae    :   10 (   8 unit;   9 type)
%            Number of atoms       :   27 (  14 equality)
%            Maximal formula depth :   16 (   4 average)
%            Number of connectives :   15 (   0   ~;   0   |;  14   &)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    2 (   1   >;   1   *;   0   +;   0  <<)
%            Number of predicates  :   13 (  11 propositional; 0-2 arity)
%            Number of functors    :   22 (  20 constant; 0-2 arity)
%            Number of variables   :    6 (   0 sgn;   6   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
%            Arithmetic symbols    :   15 (   2 pred;    0 func;   13 numbers)
% SPC      : TFF_THM_EQU_ARI

% Comments :
%------------------------------------------------------------------------------
tff(city_type,type,(
    city: $tType )).

tff(d_type,type,(
    d: ( city * city ) > $int )).

tff(kiel_type,type,(
    kiel: city )).

tff(hamburg_type,type,(
    hamburg: city )).

tff(berlin_type,type,(
    berlin: city )).

tff(cologne_type,type,(
    cologne: city )).

tff(frankfurt_type,type,(
    frankfurt: city )).

tff(saarbruecken_type,type,(
    saarbruecken: city )).

tff(munich_type,type,(
    munich: city )).

tff(city_distance_1,conjecture,
    ( ( ! [X: city,Y: city] : d(X,Y) = d(Y,X)
      & ! [X: city,Y: city,Z: city] : $lesseq(d(X,Z),$sum(d(X,Y),d(Y,Z)))
      & ! [X: city] : d(X,X) = 0
      & d(berlin,munich) = 510
      & d(berlin,cologne) = 480
      & d(berlin,frankfurt) = 420
      & d(saarbruecken,frankfurt) = 160
      & d(saarbruecken,cologne) = 190
      & d(hamburg,cologne) = 360
      & d(hamburg,frankfurt) = 390
      & d(cologne,frankfurt) = 150
      & d(hamburg,kiel) = 90
      & d(hamburg,berlin) = 250
      & d(munich,frankfurt) = 300
      & d(munich,saarbruecken) = 360 )
   => $lesseq(d(cologne,berlin),500) )).

%------------------------------------------------------------------------------
