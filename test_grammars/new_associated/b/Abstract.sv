grammar new_associated:b;


imports new_associated:host;


abstract production p1_b
top::NT1 ::=
{
  forwards to p1_host();
}

abstract production p1_b2
top::NT1 ::= why_not::NT1
{
  forwards to p1_host();
}


abstract production p2_b
top::NT2 ::=
{
  forwards to p2_host();
}

