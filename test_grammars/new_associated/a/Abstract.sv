grammar new_associated:a;


imports new_associated:host;


abstract production p1_a
top::NT1 ::= c::NT2
{
  c.i = true;
  forwards to p1_host();
}

