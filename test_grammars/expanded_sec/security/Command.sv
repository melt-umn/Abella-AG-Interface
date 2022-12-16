grammar expanded_sec:security;

aspect production noop
top::C ::=
{

}


aspect production seq
top::C ::= c1::C c2::C
{

}


aspect production declare
top::C ::= v::String ty::Type e::Expr
{

}


abstract production declareSec
top::C ::= v::String ty::Type s::SecurityLevel e::Expr
{
  forwards to declare(v, ty, e);
}


aspect production assign
top::C ::= v::String e::Expr
{

}


aspect production ifThenElse
top::C ::= cond::Expr th::C el::C
{

}


aspect production while
top::C ::= cond::Expr body::C
{

}


aspect production recUpdate
top::C ::= rec::String fields::RecFields e::Expr
{

}


aspect production printVal
top::C ::= e::Expr
{

}





aspect production oneField
top::RecFields ::= field::String
{

}


aspect production addField
top::RecFields ::= field::String rest::RecFields
{

}
