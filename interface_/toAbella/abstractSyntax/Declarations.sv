grammar interface_:toAbella:abstractSyntax;


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





attribute
   eqTest<Type>, isEq
occurs on Type;

aspect production arrowType
top::Type ::= ty1::Type ty2::Type
{
  ty1.eqTest =
      case top.eqTest of
      | arrowType(x, _) -> x
      | _ -> error("Should not need eqTest on ty1 unless top.eqTest is an arrow")
      end;
  ty2.eqTest =
      case top.eqTest of
      | arrowType(_, x) -> x
      | _ -> error("Should not need eqTest on ty2 unless top.eqTest is an arrow")
      end;
  top.isEq =
     case top.eqTest of
     | arrowType(_, _) -> ty1.isEq && ty2.isEq
     | underscoreType() -> true
     | _ -> false
     end;
}


aspect production nameType
top::Type ::= name::String
{
  top.isEq =
     case top.eqTest of
     | nameType(n) -> n == name
     | underscoreType() -> true
     | _ -> false
     end;
}


aspect production functorType
top::Type ::= functorTy::Type argTy::Type
{
  functorTy.eqTest =
      case top.eqTest of
      | functorType(x, _) -> x
      | _ -> error("Should not need eqTest on functorTy unless top.eqTest is a functor application")
      end;
  argTy.eqTest =
      case top.eqTest of
      | functorType(_, x) -> x
      | _ -> error("Should not need eqTest on argTy unless top.eqTest is a functor application")
      end;
  top.isEq =
     case top.eqTest of
     | functorType(_, _) -> functorTy.isEq && argTy.isEq
     | underscoreType() -> true
     | _ -> false
     end;
}


aspect production underscoreType
top::Type ::=
{
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

