grammar new_associated:host;


{-
  The point of this example is to test that imported attributes which
  become newly associated with an imported noterminal in a new
  grammar.
-}

inherited attribute i::Boolean;

nonterminal NT1;

nonterminal NT2 with i;


abstract production p1_host
top::NT1 ::=
{

}


abstract production p2_host
top::NT2 ::=
{

}



