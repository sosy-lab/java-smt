%------------------------------------------------------------------------------
% File     : PHI009+1 : TPTP v8.1.2. Released v7.2.0.
% Domain   : Philosophy
% Problem  : Lemma for Anselm's ontological argument
% Version  : [Wol16] axioms.
% English  :

% Refs     : [OZ11]  Oppenheimer & Zalta (2011), A Computationally-Discover
%          : [Wol16] Woltzenlogel Paleo (2016), Email to Geoff Sutcliffe
% Source   : [Wol16]
% Names    : descripthm1.p [Wol16]

% Status   : Theorem
% Rating   : 0.11 v8.1.0, 0.06 v7.4.0, 0.07 v7.2.0
% Syntax   : Number of formulae    :    2 (   0 unt;   0 def)
%            Number of atoms       :   19 (   2 equ)
%            Maximal formula atoms :   11 (   9 avg)
%            Number of connectives :   17 (   0   ~;   0   |;   9   &)
%                                         (   1 <=>;   7  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   13 (  12 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    5 (   4 usr;   0 prp; 1-2 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    9 (   6   !;   3   ?)
% SPC      : FOF_THM_RFO_SEQ

% Comments : See http://mally.stanford.edu/cm/ontological-argument/
%------------------------------------------------------------------------------
fof(description_axiom_schema_instance,axiom,
    ! [F,G,X] :
      ( ( property(F)
        & property(G)
        & object(X) )
     => ( ( is_the(X,F)
          & exemplifies_property(G,X) )
      <=> ? [Y] :
            ( object(Y)
            & exemplifies_property(F,Y)
            & ! [Z] :
                ( object(Z)
               => ( exemplifies_property(F,Z)
                 => Z = Y ) )
            & exemplifies_property(G,Y) ) ) ) ).

fof(description_theorem_1,conjecture,
    ! [F] :
      ( property(F)
     => ( ? [Y] :
            ( object(Y)
            & exemplifies_property(F,Y)
            & ! [Z] :
                ( object(Z)
               => ( exemplifies_property(F,Z)
                 => Z = Y ) ) )
       => ? [U] :
            ( object(U)
            & is_the(U,F) ) ) ) ).

%------------------------------------------------------------------------------
