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
   translation<Type>, errors, knownTyParams,
   eqTest<Type>, isEq,
   argumentTypes, headTypeName, resultType,
   isRelation
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

  top.translation = arrowType(ty1.translation, ty2.translation);

  top.argumentTypes = ty1::ty2.argumentTypes;

  top.headTypeName = nothing();

  top.resultType = ty2.resultType;

  top.isRelation = left("Is relations are not defined for arrow types");
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

  top.translation =
      if name == "string"
      then functorType(nameType("list"), nameType("$char"))
      else if isCapitalized(name) && !contains(name, top.knownTyParams)
           then --capitalized non-parameters must be nonterminals
                nameType(nameToNonterminalName(name))
           else nameType(name);

  top.errors <-
      if startsWith("$", name)
      then [errorMsg("Identifiers cannot start with \"$\"")]
      else [];

  top.argumentTypes = [];

  top.headTypeName = just(name);

  top.resultType = top;

  top.isRelation =
      case name of
      | "string" -> right(nameTerm("is_string", nothing()))
      | "list" -> right(nameTerm("is_list", nothing()))
      | "pair" -> right(nameTerm("is_pair", nothing()))
      | "integer" -> right(nameTerm("is_integer", nothing()))
      | "bool" -> right(nameTerm("is_bool", nothing()))
      | _ -> left("Cannot generate is relation for type " ++ name)
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

  top.translation = functorType(functorTy.translation, argTy.translation);

  top.argumentTypes = [];

  top.headTypeName = functorTy.headTypeName;

  top.resultType = top;

  top.isRelation =
      case functorTy, argTy of
      | nameType("list"), nameType("$char") ->
        right(nameTerm("is_string", nothing()))
      | _, _ ->
        case functorTy.isRelation, argTy.isRelation of
        | right(fis), right(ais) ->
          right(buildApplication(fis, [ais]))
        | left(str), _ -> left(str)
        | _, left(str) -> left(str)
        end
      end;
}


aspect production underscoreType
top::Type ::=
{
  top.isEq = true;

  top.translation = underscoreType();

  top.argumentTypes = [];

  top.headTypeName = nothing();

  top.resultType = top;

  top.isRelation = left("Cannot generate is relation for underscore type");
}





nonterminal Defs with pp, silverContext;

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





nonterminal Def with pp, silverContext;

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

