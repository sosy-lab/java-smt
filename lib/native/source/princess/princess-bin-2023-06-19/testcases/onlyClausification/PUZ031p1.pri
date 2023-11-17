// This file is part of KeY - Integrated Deductive Software Design 
// Copyright (C) 2001 Universitaet Karlsruhe, Germany
//                    and Chalmers University of Technology, Sweden          
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

// File     : PUZ031+1 : TPTP v2.5.0. Released v2.0.0.
// Domain   : Puzzles
// Problem  : Schubert's Steamroller
// Version  : Especial.
// English  : Wolves, foxes, birds, caterpillars, and snails are animals, and
//            there are some of each of them. Also there are some grains, and
//            grains are plants. Every animal either likes to eat \forall S plants
//            or \forall S animals much smaller than itself that like to eat some
//            plants. Caterpillars and snails are much smaller than birds,
//            which are much smaller than foxes, which in turn are much
//            smaller than wolves. Wolves do not like to eat foxes or grains,
//            while birds like to eat caterpillars but not snails.
//            Caterpillars and snails like to eat some plants. Therefore
//            there is an animal that likes to eat a grain eating animal.





\predicates {
  wolf(int);
  animal(int);
  fox(int);
  bird(int);
  caterpillar(int);
  snail(int);
  grain(int);
  plant(int);
  eats(int,int);
  much_smaller(int,int);
}


\problem {
     \forall int X;  (wolf(X) -> animal(X))
   & \exists int X1;  wolf(X1)
   & \forall int X;  (fox(X) -> animal(X))
   & \exists int X1;  fox(X1)
   & \forall int X;  (bird(X) -> animal(X))
   & \exists int X1;  bird(X1)
   & \forall int X;  (caterpillar(X) -> animal(X))
   & \exists int X1;  caterpillar(X1)
   & \forall int X;  (snail(X) -> animal(X))
   & \exists int X1;  snail(X1)
   & \exists int X;  grain(X)
   & \forall int X1;  (grain(X1) -> plant(X1))
   & \forall int X; 
       (   animal(X)
        ->   \forall int Y;  (plant(Y) -> eats(X, Y))
           | \forall int Y1; 
               (     (animal(Y1) & much_smaller(Y1, X))
                   & \exists int Z;  (plant(Z) & eats(Y1, Z))
                -> eats(X, Y1)))
   & \forall int X; 
       \forall int Y; 
         (   bird(Y) & (snail(X) | caterpillar(X))
          -> much_smaller(X, Y))
   & \forall int X; 
       \forall int Y; 
         (bird(X) & fox(Y) -> much_smaller(X, Y))
   & \forall int X; 
       \forall int Y; 
         (fox(X) & wolf(Y) -> much_smaller(X, Y))
   & \forall int X; 
       \forall int Y; 
         (wolf(X) & (fox(Y) | grain(Y)) -> !eats(X, Y))
   & \forall int X; 
       \forall int Y; 
         (bird(X) & caterpillar(Y) -> eats(X, Y))
   & \forall int X; 
       \forall int Y;  (bird(X) & snail(Y) -> !eats(X, Y))
   & \forall int X; 
       (   caterpillar(X)
         | snail(X)
        -> \exists int Y;  (plant(Y) & eats(X, Y)))
-> \exists int X; 
     \exists int Y; 
       (  (animal(X) & animal(Y))
        & \exists int Z; 
            ((grain(Z) & eats(Y, Z)) & eats(X, Y)))

}

