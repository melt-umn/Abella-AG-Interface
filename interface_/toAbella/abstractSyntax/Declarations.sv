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
   translation<Type>, errors, knownTyParams, fullType,
   --colonFullNames here is fullType without $nt_ on nonterminals
   colonFullNames,
   colonType, encodedType,
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

  top.fullType = arrowType(ty1.fullType, ty2.fullType);

  top.colonFullNames = arrowType(ty1.colonFullNames, ty2.colonFullNames);

  top.colonType = arrowType(ty1.colonType, ty2.colonType);
  top.encodedType = arrowType(ty1.encodedType, ty2.encodedType);

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
           case findNonterminal(name, top.silverContext) of
           | [nt] -> nameType(nameToNonterminalName(nt))
           | _ -> error("Should not access translation in presence of errors 1 (nameType(" ++ name ++ "))")
           end
      else if isFullyQualifiedName(name) && isCapitalized(splitQualifiedName(name).2)
      then case findNonterminal(name, top.silverContext) of
           | [nt] -> nameType(nameToNonterminalName(nt))
           | _ -> error("Should not access translation in presence of errors 2 (nameType(" ++ name ++ "))\n\n" ++ top.silverContext.pp)
           end
      else nameType(colonsToEncoded(name));

  top.fullType =
      if isCapitalized(name) && !contains(name, top.knownTyParams)
      then --capitalized non-parameters must be nonterminals
           case findNonterminal(name, top.silverContext) of
           | [nt] -> nameType(nameToColonNonterminalName(nt))
           | _ -> error("Should not access fullType in presence of errors (nameType(" ++ name ++ "))")
           end
      else if isFullyQualifiedName(name) && isCapitalized(splitQualifiedName(name).2)
      then nameType(nameToColonNonterminalName(name))
      else nameType(name);

  top.colonFullNames =
      case top.fullType of
      | nameType(n) when nameIsNonterminal(n) ->
        nameType(nonterminalNameToName(n)) --remove $nt_
      | _ -> top.fullType
      end;

  top.colonType = nameType(encodedToColons(name));
  top.encodedType = nameType(colonsToEncoded(name));

  top.errors <-
      if indexOf("$", name) >= 0
      then [errorMsg("Identifiers cannot contain \"$\"")]
      else [];
  top.errors <-
      if isCapitalized(name) && !contains(name, top.knownTyParams)
      then case findNonterminal(name, top.silverContext) of
           | [] -> [errorMsg("No nonterminal type " ++ name)]
           | [_] -> []
           | lst -> [errorMsg("Undetermined nonterminal type " ++ name ++
                              "; choices are " ++ implode(", ", lst))]
           end
      else [];
  top.errors <-
      if isFullyQualifiedName(name) && isCapitalized(splitQualifiedName(name).2)
      then case findNonterminal(name, top.silverContext) of
           | [nt] -> []
           | _ -> [errorMsg("Unknown nonterminal " ++ name)]
           end
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

  top.fullType = functorType(functorTy.fullType, argTy.fullType);

  top.colonFullNames = functorType(functorTy.colonFullNames, argTy.colonFullNames);

  top.colonType = functorType(functorTy.colonType, argTy.colonType);
  top.encodedType = functorType(functorTy.encodedType, argTy.encodedType);

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

  top.fullType = underscoreType();

  top.colonFullNames = underscoreType();

  top.colonType = underscoreType();
  top.encodedType = underscoreType();

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

  clausehead.knownTrees = [];
  clausehead.boundVars = [];
  clausehead.finalTys =
             map(\ l::[(String, Maybe<[Type]>)] ->
                   map(\ p::(String, Maybe<[Type]>) ->
                         (p.1, bind(p.2, \ l::[Type] -> just(head(l)))), l),
                 clausehead.boundVarsOut);
  clausehead.knownDecoratedTrees = [];
  clausehead.knownNames = [];
  clausehead.knownTyParams = [];
}


abstract production ruleDef
top::Def ::= clausehead::Metaterm body::Metaterm
{
  top.pp = clausehead.pp ++ " := " ++ body.pp;

  clausehead.knownTrees = [];
  clausehead.boundVars = [];
  clausehead.finalTys =
             map(\ l::[(String, Maybe<[Type]>)] ->
                   map(\ p::(String, Maybe<[Type]>) ->
                         (p.1, bind(p.2, \ l::[Type] -> just(head(l)))), l),
                 clausehead.boundVarsOut);
  clausehead.knownDecoratedTrees = [];
  clausehead.knownNames = [];
  clausehead.knownTyParams = [];

  body.knownTrees = [];
  body.boundVars = [];
  body.finalTys =
       map(\ l::[(String, Maybe<[Type]>)] ->
             map(\ p::(String, Maybe<[Type]>) ->
                   (p.1, bind(p.2, \ l::[Type] -> just(head(l)))), l),
           body.boundVarsOut ++ clausehead.boundVarsOut);
  body.knownDecoratedTrees = [];
  body.knownNames = [];
  body.knownTyParams = [];
}

