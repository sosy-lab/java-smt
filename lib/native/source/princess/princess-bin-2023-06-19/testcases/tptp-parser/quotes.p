tff('Pair',type,(
    'Pair[Int,Int]': $tType )).

tff('Color',type,(
    'Color': $tType )).

tff(red,type,(
    'red:Color': 'Color' )).

tff(green,type,(
    'green:\\\\\'Color\'': 'Color' )).

tff(green,type,(
    'blue:\\\\\'Color\'': 'Color' )).

tff(first,type,(
    'first:(Pair[Int,Int])>Int': 'Pair[Int,Int]' > $int )).

tff(formula_032,axiom,(
    'red:Color' != 'green:\\\\\'Color\'' )).
