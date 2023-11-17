%------------------------------------------------------------------------------
% File     : GEO212+3 : TPTP v6.1.0. Released v4.0.0.
% Domain   : Geometry (Constructive)
% Problem  : Non-orthogonal lines and a third line
% Version  : [vPl95] axioms.
% English  : If a line L is not orthogonal to M, then a third line N is
%            convergent to L or not orthogonal to M.

% Refs     : [vPl95] von Plato (1995), The Axioms of Constructive Geometry
%          : [ROK06] Raths et al. (2006), The ILTP Problem Library for Intu
%          : [Rat07] Raths (2007), Email to Geoff Sutcliffe
% Source   : [Rat07]
% Names    : Theorem 8.3 [vPl95]

% Status   : CounterSatisfiable
% Rating   : 0.22 v6.1.0, 0.10 v6.0.0, 0.00 v5.5.0, 0.29 v5.4.0, 0.80 v5.3.0, 0.85 v5.2.0, 0.62 v5.0.0, 0.56 v4.1.0, 0.33 v4.0.1, 0.67 v4.0.0
% Syntax   : Number of formulae    :   36 (   7 unit)
%            Number of atoms       :   96 (   0 equality)
%            Maximal formula depth :    9 (   5 average)
%            Number of connectives :   88 (  28   ~;  20   |;  13   &)
%                                         (   5 <=>;  22  =>;   0  <=)
%                                         (   0 <~>;   0  ~|;   0  ~&)
%            Number of predicates  :   13 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   0 constant; 2-2 arity)
%            Number of variables   :   84 (   0 sgn;  84   !;   0   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_CSA_RFO_NEQ

% Comments : Intuitively this is a theorem, so the encoding must be bugged.
%------------------------------------------------------------------------------
%include('Axioms/GEO006+0.ax').

%include('Axioms/GEO006+1.ax').

%include('Axioms/GEO006+2.ax').

%include('Axioms/GEO006+3.ax').
  
%include('Axioms/GEO006+4.ax').

%----Transitivity of nonobliqueness
fof(cotno1,axiom,(
    ! [L,M,N] :
      ( ( ( convergent_lines(L,M)
          & unorthogonal_lines(L,M) )
        | ( convergent_lines(L,N)
          & unorthogonal_lines(L,N) ) )
     <= ( convergent_lines(M,N)
        & unorthogonal_lines(M,N) ) ) )).

%include('Axioms/GEO006+5.ax').

%include('Axioms/GEO006+6.ax').

fof(a3,axiom,(
    ! [X,Y] :
      ( parallel_lines(X,Y)
    <=> ~ convergent_lines(X,Y) ) )).

fof(a5,axiom,(
    ! [X,Y] :
      ( orthogonal_lines(X,Y)
    <=> ~ unorthogonal_lines(X,Y) ) )).
   
%------------------------------------------------------------------------------
fof(con,conjecture,(
    ! [L,M,N] :
      ( not_orthogonal_lines(L,M)
     => ( convergent_lines(L,N)
        | not_orthogonal_lines(M,N) ) ) )).

%------------------------------------------------------------------------------
