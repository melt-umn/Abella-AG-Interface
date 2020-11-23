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





nonterminal Type with
   pp,
   eqTest<Type>, isEq;

abstract production arrowType
top::Type ::= ty1::Type ty2::Type
{
  top.pp = "(" ++ ty1.pp ++ ") -> " ++ ty2.pp;

  ty1.eqTest = case top.eqTest of | arrowType(x, _) -> x end;
  ty2.eqTest = case top.eqTest of | arrowType(_, x) -> x end;
  top.isEq =
     case top.eqTest of
     | arrowType(_, _) -> ty1.isEq && ty2.isEq
     | underscoreType() -> true
     | _ -> false
     end;
}


abstract production nameType
top::Type ::= name::String
{
  top.pp = name;

  top.isEq =
     case top.eqTest of
     | nameType(n) -> n == name
     | underscoreType() -> true
     | _ -> false
     end;
}


abstract production functorType
top::Type ::= functorTy::Type argTy::Type
{
  top.pp = functorTy.pp ++ " (" ++ argTy.pp ++ ")";

  functorTy.eqTest = case top.eqTest of | functorType(x, _) -> x end;
  argTy.eqTest = case top.eqTest of | functorType(_, x) -> x end;
  top.isEq =
     case top.eqTest of
     | functorType(_, _) -> functorTy.isEq && argTy.isEq
     | underscoreType() -> true
     | _ -> false
     end;
}


abstract production underscoreType
top::Type ::=
{
  top.pp = "_";

  top.isEq = true;
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

