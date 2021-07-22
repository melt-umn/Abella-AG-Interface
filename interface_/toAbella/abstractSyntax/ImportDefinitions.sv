grammar interface_:toAbella:abstractSyntax;

{-
  This file is to allow us to read in definitions from Abella files.
  We want to read the file in, parse it, then run through it to gather
  the nonterminals, productions, and attributes declared to build our
  ProverState.

  We do this in a separate file because the attributes here have to do
  with reading a file, not interactively proving as we see in the
  other files.

  IMPORTANT:  This will *only* work with grammar encodings which are
  correctly defined.  If it does not follow the prescribed format, we
  might miss something or add something which is not supposed to be
  added.
-}

monoid attribute newAttrs::[String] with [], ++;
propagate newAttrs on ListOfCommands, AnyCommand, TopCommand;


monoid attribute newAttrOccurrences::[(String, [(Type, Type)])]
       with [], combineAssociations(_, _);
propagate newAttrOccurrences on ListOfCommands, AnyCommand, TopCommand;

function combineAssociations
[(String, [a])] ::= l1::[(String, [a])] l2::[(String, [a])]
{
  return
     case l1 of
     | [] -> l2
     | (s, lst)::t ->
       case findAssociated(s, l2) of
       | nothing() -> combineAssociations(t, (s, lst)::l2)
       | just(lst2) ->
         combineAssociations(t,
            replaceAssociated(s, lst ++ lst2, l2).fromJust)
       end
     end;
}

monoid attribute newInheritedAttrs::[String] with [], ++;
propagate newInheritedAttrs on ListOfCommands, AnyCommand, TopCommand;

monoid attribute newLocalAttrs::[(String, [(String, Type)])]
       with [], combineAssociations(_, _);
propagate newLocalAttrs on ListOfCommands, AnyCommand, TopCommand;

monoid attribute newProductions::[(String, Type)] with [], ++;
propagate newProductions on ListOfCommands, AnyCommand, TopCommand;


monoid attribute newWPDRelations::[(String, Type, [String])] with [], ++;
propagate newWPDRelations on ListOfCommands, AnyCommand, TopCommand;


monoid attribute newTheorems::[(String, Metaterm)] with [], ++;
propagate newTheorems on ListOfCommands, AnyCommand, TopCommand;


monoid attribute newFunctions::[(String, Type)] with [], ++;
propagate newFunctions on ListOfCommands, AnyCommand, TopCommand;





nonterminal ListOfCommands with
   newAttrs, newAttrOccurrences, newProductions, newWPDRelations,
      newTheorems, newInheritedAttrs, newLocalAttrs, newFunctions,
   numCommandsSent,
   pp,
   commandList;

synthesized attribute commandList::[AnyCommand];


abstract production emptyListOfCommands
top::ListOfCommands ::=
{
  top.pp = "";

  top.numCommandsSent = 0;

  top.commandList = [];
}


abstract production addListOfCommands
top::ListOfCommands ::= a::AnyCommand rest::ListOfCommands
{
  top.pp = a.pp ++ rest.pp;

  top.numCommandsSent = 1 + rest.numCommandsSent;

  top.commandList = a::rest.commandList;
}


abstract production joinListOfCommands
top::ListOfCommands ::= l1::ListOfCommands l2::ListOfCommands
{
  top.pp = l1.pp ++ l2.pp;

  top.numCommandsSent = l1.numCommandsSent + l2.numCommandsSent;

  top.commandList = l1.commandList ++ l2.commandList;
}





attribute
   newAttrs, newAttrOccurrences, newProductions, newWPDRelations,
      newTheorems, newInheritedAttrs, newLocalAttrs, newFunctions
occurs on AnyCommand;





attribute
   newAttrs, newAttrOccurrences, newProductions, newWPDRelations,
      newTheorems, newInheritedAttrs, newLocalAttrs, newFunctions
occurs on TopCommand;

aspect production theoremDeclaration
top::TopCommand ::= name::String params::[String] body::Metaterm
{
  --Grammar files don't have Split commands, so this is the only new theorem place
  top.newTheorems <- [(name, new(body))];
}

aspect production definitionDeclaration
top::TopCommand ::= preds::[(String, Type)] defs::Defs
{
  top.newWPDRelations <-
      case preds of
      | [] -> [] --probably shouldn't get this
      --Catches the components because of how isWpdTypeName checks
      | [(name, arrowType(ty, _))] when isWpdTypeName(name) ->
        [(name, ty, defs.wpdProdNames)]
        --aren't mutual in components, so can't be in longer list
      | _ -> []
      end;

  top.newFunctions <-
      foldr(\ p::(String, Type) rest::[(String, Type)] ->
              if isFun(p.1)
              then (funToName(p.1), p.2)::rest
              else rest,
            [], preds);
}


aspect production typeDeclaration
top::TopCommand ::= names::[String] ty::Type
{
  top.newProductions <-
      if tyIsNonterminal(ty.resultType)
      then map(\ s::String -> pair(prodToName(s), ty), names)
      else [];

  local attrTy::Type =
        case ty of
        | arrowType(_, arrowType(_, arrowType(functorType(_, attrty), _))) ->
          new(attrty)
        | _ -> error("Access relations must have types of a certain form")
        end;

  top.newAttrs <-
      foldr(\ s::String rest::[String] ->
              if isAccessRelation(s)
              then accessRelationToAttr(s)::rest
              else rest,
            [], names);

  top.newAttrOccurrences <-
      --combining occurrence information for same attr happens by monoid join function
      foldr(\ s::String rest::[(String, [(Type, Type)])] ->
              if isAccessRelation(s)
              then (accessRelationToAttr(s),
                    [(nameType(accessRelationToType(s)),
                      new(attrTy))])::rest
              else rest,
            [], names);

  top.newInheritedAttrs <-
      foldr(\ s::String rest::[String] ->
              if endsWith("$_is_inherited", s)
              then substring(1, lastIndexOf("$", s), s)::rest
              else rest,
            [], names);

  top.newLocalAttrs <-
      foldr(\ s::String rest::[(String, [(String, Type)])] ->
              if isLocalAccessRelation(s)
              then (localAccessToAttr(s),
                    [(localAccessToProd(s),
                     case attrTy of
                     | functorType(functorType(nameType("$pair"), ntTy), _)
                       when tyIsNonterminal(ntTy) ->
                       ntTy
                     | ty -> new(ty)
                     end)])::rest
              else rest,
            [], names);
}





synthesized attribute wpdProdNames::[String];

attribute
   wpdProdNames
occurs on Defs;

aspect production singleDefs
top::Defs ::= d::Def
{
  top.wpdProdNames = d.wpdProdNames;
}


aspect production consDefs
top::Defs ::= d::Def rest::Defs
{
  top.wpdProdNames = d.wpdProdNames ++ rest.wpdProdNames;
}





attribute
   wpdProdNames
occurs on Def;

aspect production factDef
top::Def ::= clausehead::Metaterm
{
  top.wpdProdNames =
      case clausehead of
      | termMetaterm(
           applicationTerm(_,
              consTermList(
                 applicationTerm(
                    nameTerm(prod, _),
                    _),
                 _)),
           _) ->
        [prodToName(prod)]
      | termMetaterm(
           applicationTerm(_,
              consTermList(
                 nameTerm(prod, _),
                 _)),
           _) ->
        [prodToName(prod)]
      | _ -> error("Should not access wpdProdNames if not WPD definition")
      end;
}


aspect production ruleDef
top::Def ::= clausehead::Metaterm body::Metaterm
{
  top.wpdProdNames =
      case clausehead of
      | termMetaterm(
           applicationTerm(_,
              consTermList(
                 applicationTerm(
                    nameTerm(prod, _),
                    _),
                 _)),
           _) ->
        [prodToName(prod)]
      | termMetaterm(
           applicationTerm(_,
              consTermList(
                 nameTerm(prod, _),
                 _)),
           _) ->
        [prodToName(prod)]
      | _ -> error("Should not access wpdProdNames if not WPD definition")
      end;
}

