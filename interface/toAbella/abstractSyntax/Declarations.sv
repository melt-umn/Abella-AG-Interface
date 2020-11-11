grammar toAbella:abstractSyntax;


nonterminal Kind with pp;

abstract production typeKind
top::Kind ::=
{
  top.pp = "type";
}


abstract production arrowKind
top::Kind ::= k::Kind
{
  top.pp = "type -> " ++ k.pp;
}





nonterminal Type with pp;

abstract production arrowType
top::Type ::= ty1::Type ty2::Type
{
  top.pp = "(" ++ ty1.pp ++ ") -> " ++ ty2.pp;
}


abstract production nameType
top::Type ::= name::String
{
  top.pp = name;
}


abstract production functorType
top::Type ::= functorTy::Type argTy::Type
{
  top.pp = functorTy.pp ++ " (" ++ argTy.pp ++ ")";
}


abstract production underscoreType
top::Type ::=
{
  top.pp = "_";
}





nonterminal Defs with pp;

abstract production singleDefs
top::Defs ::= d::Def
{
  top.pp = d.pp;
}


abstract production consDefs
top::Defs ::= d::Def rest::Defs
{
  top.pp = d.pp ++ "; " ++ rest.pp;
}





nonterminal Def with pp;

abstract production factDef
top::Def ::= clausehead::Metaterm
{
  top.pp = clausehead.pp;
}


abstract production ruleDef
top::Def ::= clausehead::Metaterm body::Metaterm
{
  top.pp = clausehead.pp ++ " := " ++ body.pp;
}

