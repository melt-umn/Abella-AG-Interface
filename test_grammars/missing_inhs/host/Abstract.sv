grammar missing_inhs:host;

{-
  This grammar is for testing inherited attributes not being given,
  making sure the relations for them are still being generated.
-}

nonterminal Expr with env;

nonterminal Stmt with env;

inherited attribute env::[(String, Integer)];


abstract production assign
top::Stmt ::= name::String e::Expr
{
  local noInhs::Expr = e;
}


abstract production seq
top::Stmt ::= s1::Stmt s2::Stmt
{
  s1.env = top.env;
}


abstract production ifThenElse
top::Stmt ::= c::Expr th::Stmt el::Stmt
{
  c.env = top.env;
  th.env = top.env;
  el.env = top.env;
}


abstract production fwding
top::Stmt ::= e::Expr
{
  forwards to assign("x", e);
}



abstract production num
top::Expr ::= i::Integer
{

}

