
\functions {
  int skF, skY;
}

\predicates {
  property(int);
  object(int);
  is_the(int, int);
  exemplifies_property(int, int);
}

\problem {

    \forall int F,G,X;
      ( ( property(F)
        & property(G)
        & object(X) )
     -> ( ( is_the(X,F)
          & exemplifies_property(G,X) )
      <-> \exists int Y;
            ( object(Y)
            & exemplifies_property(F,Y)
            & \forall int Z;
                ( object(Z)
               -> ( exemplifies_property(F,Z)
                 -> Z = Y ) )
            & exemplifies_property(G,Y) ) ) )

  ->


      ( property(skF)
     -> ( 
            ( object(skY)
            & exemplifies_property(skF,skY)
            & \forall int Z;
                ( object(Z)
               -> ( exemplifies_property(skF,Z)
                 -> Z = skY ) ) )
       -> \exists int U;
            ( object(U)
            & is_the(U,skF) ) ) )
}


