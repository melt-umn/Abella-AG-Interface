grammar expanded_sec:security;

aspect production num
top::Expr ::= i::Integer
{

}


aspect production plus
top::Expr ::= e1::Expr e2::Expr
{

}


aspect production name
top::Expr ::= v::String
{

}


aspect production greater
top::Expr ::= e1::Expr e2::Expr
{

}


aspect production eqCheck
top::Expr ::= e1::Expr e2::Expr
{

}


aspect production and
top::Expr ::= e1::Expr e2::Expr
{

}


aspect production or
top::Expr ::= e1::Expr e2::Expr
{

}


aspect production etrue
top::Expr ::=
{

}


aspect production efalse
top::Expr ::=
{

}


aspect production call
top::Expr ::= funName::String args::Args
{

}


aspect production recBuild
top::Expr ::= contents::RecFieldExprs
{

}


aspect production recFieldAccess
top::Expr ::= rec::Expr field::String
{

}





aspect production endRecFieldExprs
top::RecFieldExprs ::=
{

}


aspect production addRecFieldExprs
top::RecFieldExprs ::= field::String e::Expr rest::RecFieldExprs
{

}





aspect production endArgs
top::Args ::=
{

}


aspect production addArgs
top::Args ::= e::Expr rest::Args
{

}
