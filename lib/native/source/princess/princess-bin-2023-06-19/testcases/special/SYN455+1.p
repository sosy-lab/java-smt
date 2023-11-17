
%--------------------------------------------------------------------------
% File     : SYN455+1 : TPTP v8.1.2. Released v2.1.0.
% Domain   : Syntactic (Translated)
% Problem  : ALC, N=4, R=1, L=60, K=3, D=1, P=0, Index=056
% Version  : Especial.
% English  :

% Refs     : [OS95]  Ohlbach & Schmidt (1995), Functional Translation and S
%          : [HS97]  Hustadt & Schmidt (1997), On Evaluating Decision Proce
%          : [Wei97] Weidenbach (1997), Email to G. Sutcliffe
% Source   : [Wei97]
% Names    : alc-4-1-60-3-1-056.dfg [Wei97]

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.17 v6.0.0, 0.00 v5.5.0, 0.33 v5.3.0, 0.27 v5.2.0, 0.00 v5.0.0, 0.25 v4.1.0, 0.44 v4.0.1, 0.42 v4.0.0, 0.45 v3.7.0, 0.67 v3.5.0, 0.38 v3.4.0, 0.25 v3.3.0, 0.22 v3.2.0, 0.33 v3.1.0, 0.67 v2.7.0, 0.33 v2.6.0, 0.00 v2.5.0, 0.33 v2.4.0, 0.33 v2.2.1, 0.50 v2.2.0, 0.00 v2.1.0
% Syntax   : Number of formulae    :    1 (   0 unt;   0 def)
%            Number of atoms       :  603 (   0 equ)
%            Maximal formula atoms :  603 ( 603 avg)
%            Number of connectives :  811 ( 209   ~; 329   |; 183   &)
%                                         (   0 <=>;  90  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   96 (  96 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :   36 (  36 usr;  32 prp; 0-1 aty)
%            Number of functors    :   31 (  31 usr;  31 con; 0-0 aty)
%            Number of variables   :   90 (  90   !;   0   ?)
% SPC      : FOF_THM_EPR_NEQ

% Comments : These ALC problems have been translated from propositional
%            multi-modal K logic formulae generated according to the scheme
%            described in [HS97], using the optimized functional translation
%            described in [OS95]. The finite model property holds, the
%            Herbrand Universe is finite, they are decidable (the complexity
%            is PSPACE-complete), resolution + subsumption + condensing is a
%            decision procedure, and the translated formulae belong to the
%            (CNF-translation of the) Bernays-Schoenfinkel class [Wei97].
%--------------------------------------------------------------------------
fof(co1,conjecture,
    ~ ( ( ~ hskp0
        | ( ndr1_0
          & ~ c0_1(a901)
          & ~ c1_1(a901)
          & ~ c3_1(a901) ) )
      & ( ~ hskp1
        | ( ndr1_0
          & c0_1(a902)
          & c2_1(a902)
          & ~ c1_1(a902) ) )
      & ( ~ hskp2
        | ( ndr1_0
          & c0_1(a903)
          & ~ c2_1(a903)
          & ~ c3_1(a903) ) )
      & ( ~ hskp3
        | ( ndr1_0
          & c0_1(a904)
          & ~ c1_1(a904)
          & ~ c2_1(a904) ) )
      & ( ~ hskp4
        | ( ndr1_0
          & c3_1(a905)
          & ~ c0_1(a905)
          & ~ c2_1(a905) ) )
      & ( ~ hskp5
        | ( ndr1_0
          & c0_1(a906)
          & c2_1(a906)
          & ~ c3_1(a906) ) )
      & ( ~ hskp6
        | ( ndr1_0
          & c0_1(a907)
          & c1_1(a907)
          & ~ c2_1(a907) ) )
      & ( ~ hskp7
        | ( ndr1_0
          & c1_1(a908)
          & ~ c2_1(a908)
          & ~ c3_1(a908) ) )
      & ( ~ hskp8
        | ( ndr1_0
          & c1_1(a909)
          & ~ c0_1(a909)
          & ~ c3_1(a909) ) )
      & ( ~ hskp9
        | ( ndr1_0
          & c2_1(a910)
          & ~ c1_1(a910)
          & ~ c3_1(a910) ) )
      & ( ~ hskp10
        | ( ndr1_0
          & c1_1(a912)
          & c2_1(a912)
          & ~ c0_1(a912) ) )
      & ( ~ hskp11
        | ( ndr1_0
          & c0_1(a914)
          & c3_1(a914)
          & ~ c2_1(a914) ) )
      & ( ~ hskp12
        | ( ndr1_0
          & c1_1(a917)
          & c3_1(a917)
          & ~ c2_1(a917) ) )
      & ( ~ hskp13
        | ( ndr1_0
          & c2_1(a921)
          & ~ c0_1(a921)
          & ~ c3_1(a921) ) )
      & ( ~ hskp14
        | ( ndr1_0
          & c3_1(a923)
          & ~ c0_1(a923)
          & ~ c1_1(a923) ) )
      & ( ~ hskp15
        | ( ndr1_0
          & c2_1(a924)
          & ~ c0_1(a924)
          & ~ c1_1(a924) ) )
      & ( ~ hskp16
        | ( ndr1_0
          & c1_1(a926)
          & c2_1(a926)
          & ~ c3_1(a926) ) )
      & ( ~ hskp17
        | ( ndr1_0
          & ~ c1_1(a936)
          & ~ c2_1(a936)
          & ~ c3_1(a936) ) )
      & ( ~ hskp18
        | ( ndr1_0
          & c1_1(a937)
          & ~ c0_1(a937)
          & ~ c2_1(a937) ) )
      & ( ~ hskp19
        | ( ndr1_0
          & c2_1(a938)
          & c3_1(a938)
          & ~ c0_1(a938) ) )
      & ( ~ hskp20
        | ( ndr1_0
          & c0_1(a939)
          & ~ c1_1(a939)
          & ~ c3_1(a939) ) )
      & ( ~ hskp21
        | ( ndr1_0
          & ~ c0_1(a946)
          & ~ c2_1(a946)
          & ~ c3_1(a946) ) )
      & ( ~ hskp22
        | ( ndr1_0
          & c2_1(a949)
          & c3_1(a949)
          & ~ c1_1(a949) ) )
      & ( ~ hskp23
        | ( ndr1_0
          & c1_1(a954)
          & c3_1(a954)
          & ~ c0_1(a954) ) )
      & ( ~ hskp24
        | ( ndr1_0
          & ~ c0_1(a959)
          & ~ c1_1(a959)
          & ~ c2_1(a959) ) )
      & ( ~ hskp25
        | ( ndr1_0
          & c0_1(a960)
          & c3_1(a960)
          & ~ c1_1(a960) ) )
      & ( ~ hskp26
        | ( ndr1_0
          & c0_1(a979)
          & c1_1(a979)
          & ~ c3_1(a979) ) )
      & ( ~ hskp27
        | ( ndr1_0
          & c1_1(a900)
          & c2_1(a900)
          & c3_1(a900) ) )
      & ( ~ hskp28
        | ( ndr1_0
          & c0_1(a916)
          & c1_1(a916)
          & c3_1(a916) ) )
      & ( ~ hskp29
        | ( ndr1_0
          & c0_1(a933)
          & c2_1(a933)
          & c3_1(a933) ) )
      & ( ~ hskp30
        | ( ndr1_0
          & c0_1(a942)
          & c1_1(a942)
          & c2_1(a942) ) )
      & ( ! [U] :
            ( ndr1_0
           => ( c0_1(U)
              | c1_1(U)
              | c2_1(U) ) )
        | ! [V] :
            ( ndr1_0
           => ( c0_1(V)
              | c2_1(V)
              | ~ c3_1(V) ) )
        | ! [W] :
            ( ndr1_0
           => ( ~ c0_1(W)
              | ~ c1_1(W)
              | ~ c3_1(W) ) ) )
      & ( ! [X] :
            ( ndr1_0
           => ( c0_1(X)
              | c1_1(X)
              | c2_1(X) ) )
        | ! [Y] :
            ( ndr1_0
           => ( c0_1(Y)
              | c3_1(Y)
              | ~ c2_1(Y) ) )
        | ! [Z] :
            ( ndr1_0
           => ( c1_1(Z)
              | c3_1(Z)
              | ~ c0_1(Z) ) ) )
      & ( ! [X1] :
            ( ndr1_0
           => ( c0_1(X1)
              | c1_1(X1)
              | c2_1(X1) ) )
        | ! [X2] :
            ( ndr1_0
           => ( c0_1(X2)
              | ~ c1_1(X2)
              | ~ c3_1(X2) ) )
        | hskp27 )
      & ( ! [X3] :
            ( ndr1_0
           => ( c0_1(X3)
              | c1_1(X3)
              | c2_1(X3) ) )
        | ! [X4] :
            ( ndr1_0
           => ( c2_1(X4)
              | ~ c0_1(X4)
              | ~ c3_1(X4) ) )
        | hskp0 )
      & ( ! [X5] :
            ( ndr1_0
           => ( c0_1(X5)
              | c1_1(X5)
              | c2_1(X5) ) )
        | ! [X6] :
            ( ndr1_0
           => ( c3_1(X6)
              | ~ c0_1(X6)
              | ~ c2_1(X6) ) )
        | ! [X7] :
            ( ndr1_0
           => ( c3_1(X7)
              | ~ c1_1(X7)
              | ~ c2_1(X7) ) ) )
      & ( ! [X8] :
            ( ndr1_0
           => ( c0_1(X8)
              | c1_1(X8)
              | c2_1(X8) ) )
        | hskp1
        | hskp2 )
      & ( ! [X9] :
            ( ndr1_0
           => ( c0_1(X9)
              | c1_1(X9)
              | c3_1(X9) ) )
        | ! [X10] :
            ( ndr1_0
           => ( c0_1(X10)
              | c2_1(X10)
              | c3_1(X10) ) )
        | ! [X11] :
            ( ndr1_0
           => ( c2_1(X11)
              | c3_1(X11)
              | ~ c0_1(X11) ) ) )
      & ( ! [X12] :
            ( ndr1_0
           => ( c0_1(X12)
              | c1_1(X12)
              | c3_1(X12) ) )
        | ! [X13] :
            ( ndr1_0
           => ( c0_1(X13)
              | ~ c1_1(X13)
              | ~ c2_1(X13) ) )
        | ! [X14] :
            ( ndr1_0
           => ( c2_1(X14)
              | c3_1(X14)
              | ~ c0_1(X14) ) ) )
      & ( ! [X15] :
            ( ndr1_0
           => ( c0_1(X15)
              | c1_1(X15)
              | ~ c2_1(X15) ) )
        | hskp3
        | hskp4 )
      & ( ! [X16] :
            ( ndr1_0
           => ( c0_1(X16)
              | c1_1(X16)
              | ~ c3_1(X16) ) )
        | ! [X17] :
            ( ndr1_0
           => ( ~ c1_1(X17)
              | ~ c2_1(X17)
              | ~ c3_1(X17) ) )
        | hskp5 )
      & ( ! [X18] :
            ( ndr1_0
           => ( c0_1(X18)
              | c1_1(X18)
              | ~ c3_1(X18) ) )
        | hskp6
        | hskp7 )
      & ( ! [X19] :
            ( ndr1_0
           => ( c0_1(X19)
              | c2_1(X19)
              | c3_1(X19) ) )
        | ! [X20] :
            ( ndr1_0
           => ( c0_1(X20)
              | ~ c1_1(X20)
              | ~ c3_1(X20) ) )
        | hskp8 )
      & ( ! [X21] :
            ( ndr1_0
           => ( c0_1(X21)
              | c2_1(X21)
              | c3_1(X21) ) )
        | ! [X22] :
            ( ndr1_0
           => ( c1_1(X22)
              | c2_1(X22)
              | ~ c0_1(X22) ) )
        | hskp9 )
      & ( ! [X23] :
            ( ndr1_0
           => ( c0_1(X23)
              | c2_1(X23)
              | c3_1(X23) ) )
        | hskp27
        | hskp10 )
      & ( ! [X24] :
            ( ndr1_0
           => ( c0_1(X24)
              | c3_1(X24)
              | ~ c1_1(X24) ) )
        | hskp6
        | hskp11 )
      & ( ! [X25] :
            ( ndr1_0
           => ( c0_1(X25)
              | c3_1(X25)
              | ~ c2_1(X25) ) )
        | ! [X26] :
            ( ndr1_0
           => ( c0_1(X26)
              | ~ c2_1(X26)
              | ~ c3_1(X26) ) )
        | hskp5 )
      & ( ! [X27] :
            ( ndr1_0
           => ( c0_1(X27)
              | c3_1(X27)
              | ~ c2_1(X27) ) )
        | hskp28
        | hskp12 )
      & ( ! [X28] :
            ( ndr1_0
           => ( c0_1(X28)
              | c3_1(X28)
              | ~ c2_1(X28) ) )
        | hskp2
        | hskp0 )
      & ( ! [X29] :
            ( ndr1_0
           => ( c0_1(X29)
              | ~ c1_1(X29)
              | ~ c2_1(X29) ) )
        | ! [X30] :
            ( ndr1_0
           => ( c1_1(X30)
              | c3_1(X30)
              | ~ c2_1(X30) ) )
        | ! [X31] :
            ( ndr1_0
           => ( c2_1(X31)
              | ~ c1_1(X31)
              | ~ c3_1(X31) ) ) )
      & ( ! [X32] :
            ( ndr1_0
           => ( c0_1(X32)
              | ~ c1_1(X32)
              | ~ c2_1(X32) ) )
        | hskp3
        | hskp13 )
      & ( ! [X33] :
            ( ndr1_0
           => ( c0_1(X33)
              | ~ c1_1(X33)
              | ~ c2_1(X33) ) )
        | hskp7
        | hskp14 )
      & ( ! [X34] :
            ( ndr1_0
           => ( c0_1(X34)
              | ~ c2_1(X34)
              | ~ c3_1(X34) ) )
        | ! [X35] :
            ( ndr1_0
           => ( ~ c1_1(X35)
              | ~ c2_1(X35)
              | ~ c3_1(X35) ) )
        | hskp15 )
      & ( ! [X36] :
            ( ndr1_0
           => ( c0_1(X36)
              | ~ c2_1(X36)
              | ~ c3_1(X36) ) )
        | hskp28
        | hskp16 )
      & ( ! [X37] :
            ( ndr1_0
           => ( c0_1(X37)
              | ~ c2_1(X37)
              | ~ c3_1(X37) ) )
        | hskp7
        | hskp13 )
      & ( ! [X38] :
            ( ndr1_0
           => ( c1_1(X38)
              | c2_1(X38)
              | c3_1(X38) ) )
        | hskp11
        | hskp27 )
      & ( ! [X39] :
            ( ndr1_0
           => ( c1_1(X39)
              | c2_1(X39)
              | c3_1(X39) ) )
        | hskp27
        | hskp9 )
      & ( ! [X40] :
            ( ndr1_0
           => ( c1_1(X40)
              | c2_1(X40)
              | ~ c0_1(X40) ) )
        | ! [X41] :
            ( ndr1_0
           => ( c1_1(X41)
              | ~ c0_1(X41)
              | ~ c3_1(X41) ) )
        | hskp29 )
      & ( ! [X42] :
            ( ndr1_0
           => ( c1_1(X42)
              | c2_1(X42)
              | ~ c0_1(X42) ) )
        | ! [X43] :
            ( ndr1_0
           => ( ~ c0_1(X43)
              | ~ c1_1(X43)
              | ~ c3_1(X43) ) )
        | hskp15 )
      & ( ! [X44] :
            ( ndr1_0
           => ( c1_1(X44)
              | c2_1(X44)
              | ~ c0_1(X44) ) )
        | hskp12
        | hskp17 )
      & ( ! [X45] :
            ( ndr1_0
           => ( c1_1(X45)
              | c2_1(X45)
              | ~ c0_1(X45) ) )
        | hskp18
        | hskp19 )
      & ( ! [X46] :
            ( ndr1_0
           => ( c1_1(X46)
              | c2_1(X46)
              | ~ c3_1(X46) ) )
        | hskp20
        | hskp18 )
      & ( ! [X47] :
            ( ndr1_0
           => ( c1_1(X47)
              | c3_1(X47)
              | ~ c0_1(X47) ) )
        | ! [X48] :
            ( ndr1_0
           => ( ~ c0_1(X48)
              | ~ c2_1(X48)
              | ~ c3_1(X48) ) )
        | hskp9 )
      & ( ! [X49] :
            ( ndr1_0
           => ( c1_1(X49)
              | c3_1(X49)
              | ~ c0_1(X49) ) )
        | hskp30
        | hskp7 )
      & ( ! [X50] :
            ( ndr1_0
           => ( c1_1(X50)
              | ~ c0_1(X50)
              | ~ c2_1(X50) ) )
        | ! [X51] :
            ( ndr1_0
           => ( c2_1(X51)
              | c3_1(X51)
              | ~ c1_1(X51) ) )
        | hskp27 )
      & ( ! [X52] :
            ( ndr1_0
           => ( c1_1(X52)
              | ~ c0_1(X52)
              | ~ c2_1(X52) ) )
        | ! [X53] :
            ( ndr1_0
           => ( c2_1(X53)
              | ~ c0_1(X53)
              | ~ c1_1(X53) ) )
        | hskp0 )
      & ( ! [X54] :
            ( ndr1_0
           => ( c1_1(X54)
              | ~ c0_1(X54)
              | ~ c3_1(X54) ) )
        | ! [X55] :
            ( ndr1_0
           => ( c2_1(X55)
              | c3_1(X55)
              | ~ c1_1(X55) ) )
        | hskp21 )
      & ( ! [X56] :
            ( ndr1_0
           => ( c1_1(X56)
              | ~ c0_1(X56)
              | ~ c3_1(X56) ) )
        | ! [X57] :
            ( ndr1_0
           => ( ~ c0_1(X57)
              | ~ c1_1(X57)
              | ~ c3_1(X57) ) )
        | hskp1 )
      & ( ! [X58] :
            ( ndr1_0
           => ( c1_1(X58)
              | ~ c0_1(X58)
              | ~ c3_1(X58) ) )
        | hskp28 )
      & ( ! [X59] :
            ( ndr1_0
           => ( c2_1(X59)
              | c3_1(X59)
              | ~ c0_1(X59) ) )
        | ! [X60] :
            ( ndr1_0
           => ( c2_1(X60)
              | ~ c1_1(X60)
              | ~ c3_1(X60) ) )
        | hskp22 )
      & ( ! [X61] :
            ( ndr1_0
           => ( c2_1(X61)
              | c3_1(X61)
              | ~ c0_1(X61) ) )
        | ! [X62] :
            ( ndr1_0
           => ( c3_1(X62)
              | ~ c0_1(X62)
              | ~ c1_1(X62) ) )
        | hskp0 )
      & ( ! [X63] :
            ( ndr1_0
           => ( c2_1(X63)
              | c3_1(X63)
              | ~ c0_1(X63) ) )
        | hskp6
        | hskp14 )
      & ( ! [X64] :
            ( ndr1_0
           => ( c2_1(X64)
              | c3_1(X64)
              | ~ c0_1(X64) ) )
        | hskp1
        | hskp23 )
      & ( ! [X65] :
            ( ndr1_0
           => ( c2_1(X65)
              | c3_1(X65)
              | ~ c1_1(X65) ) )
        | ! [X66] :
            ( ndr1_0
           => ( c2_1(X66)
              | ~ c1_1(X66)
              | ~ c3_1(X66) ) ) )
      & ( ! [X67] :
            ( ndr1_0
           => ( c2_1(X67)
              | c3_1(X67)
              | ~ c1_1(X67) ) )
        | ! [X68] :
            ( ndr1_0
           => ( c3_1(X68)
              | ~ c0_1(X68)
              | ~ c2_1(X68) ) )
        | ! [X69] :
            ( ndr1_0
           => ( ~ c0_1(X69)
              | ~ c1_1(X69)
              | ~ c3_1(X69) ) ) )
      & ( ! [X70] :
            ( ndr1_0
           => ( c2_1(X70)
              | c3_1(X70)
              | ~ c1_1(X70) ) )
        | ! [X71] :
            ( ndr1_0
           => ( ~ c1_1(X71)
              | ~ c2_1(X71)
              | ~ c3_1(X71) ) )
        | hskp16 )
      & ( ! [X72] :
            ( ndr1_0
           => ( c2_1(X72)
              | c3_1(X72)
              | ~ c1_1(X72) ) )
        | hskp30
        | hskp9 )
      & ( ! [X73] :
            ( ndr1_0
           => ( c2_1(X73)
              | ~ c0_1(X73)
              | ~ c1_1(X73) ) )
        | hskp30
        | hskp24 )
      & ( ! [X74] :
            ( ndr1_0
           => ( c2_1(X74)
              | ~ c0_1(X74)
              | ~ c3_1(X74) ) )
        | ! [X75] :
            ( ndr1_0
           => ( c3_1(X75)
              | ~ c0_1(X75)
              | ~ c1_1(X75) ) )
        | hskp25 )
      & ( ! [X76] :
            ( ndr1_0
           => ( c2_1(X76)
              | ~ c0_1(X76)
              | ~ c3_1(X76) ) )
        | hskp1
        | hskp10 )
      & ( ! [X77] :
            ( ndr1_0
           => ( c2_1(X77)
              | ~ c0_1(X77)
              | ~ c3_1(X77) ) )
        | hskp5
        | hskp7 )
      & ( ! [X78] :
            ( ndr1_0
           => ( c2_1(X78)
              | ~ c1_1(X78)
              | ~ c3_1(X78) ) )
        | hskp25
        | hskp21 )
      & ( ! [X79] :
            ( ndr1_0
           => ( c2_1(X79)
              | ~ c1_1(X79)
              | ~ c3_1(X79) ) )
        | hskp10
        | hskp21 )
      & ( ! [X80] :
            ( ndr1_0
           => ( c3_1(X80)
              | ~ c0_1(X80)
              | ~ c1_1(X80) ) )
        | hskp27
        | hskp13 )
      & ( ! [X81] :
            ( ndr1_0
           => ( c3_1(X81)
              | ~ c0_1(X81)
              | ~ c2_1(X81) ) )
        | hskp30
        | hskp17 )
      & ( ! [X82] :
            ( ndr1_0
           => ( c3_1(X82)
              | ~ c1_1(X82)
              | ~ c2_1(X82) ) )
        | hskp20
        | hskp8 )
      & ( ! [X83] :
            ( ndr1_0
           => ( ~ c0_1(X83)
              | ~ c2_1(X83)
              | ~ c3_1(X83) ) )
        | hskp23
        | hskp15 )
      & ( ! [X84] :
            ( ndr1_0
           => ( ~ c1_1(X84)
              | ~ c2_1(X84)
              | ~ c3_1(X84) ) )
        | hskp11
        | hskp12 )
      & ( hskp26
        | hskp5
        | hskp21 )
      & ( hskp20
        | hskp14
        | hskp4 )
      & ( hskp12
        | hskp13
        | hskp21 ) ) ).

%--------------------------------------------------------------------------

