grammar interface_:toAbella:abstractSyntax;

{-
  This file is to allow us to read in definitions from Abella files.
  We want to read the file in, parse it, then run through it to gather
  the nonterminals, productions, and attributes declared to build our
  SilverContext.

  We do this in a separate file because the attributes here have to do
  with reading a file, not proving as we see in the other files.

  IMPORTANT:  This will *only* work with grammar encodings which are
  correctly defined.  If it does not follow the prescribed format, we
  might miss something or add something which is not supposed to be
  added.  Therefore only use files generated by the Silver encoding,
  not anything handwritten.
-}

function buildSilverContext
SilverContext ::= currentGrammar::String comms::ListOfCommands
{
  --We shouldn't actually need a silver context when importing,
  --   but it makes MWDA happy
  comms.silverContext = decorate emptySilverContext() with {};
  return
     silverContext(
        currentGrammar,
        comms.newAttrs,
        comms.newAttrOccurrences,
        comms.newProductions,
        comms.newFunctions,
        comms.newWPDRelations,
        comms.newInheritedAttrs,
        comms.newLocalAttrs);
}



monoid attribute newAttrs::[(String, String)] with [], ++;
propagate newAttrs on ListOfCommands, AnyCommand, TopCommand;


monoid attribute newAttrOccurrences::[(String, String, [(Type, Type)])]
       with [], combineAssociations_splitGrammar(_, _);
propagate newAttrOccurrences on ListOfCommands, AnyCommand, TopCommand;

function combineAssociations_splitGrammar
[(String, String, [a])] ::= l1::[(String, String, [a])] l2::[(String, String, [a])]
{
  return
     case l1 of
     | [] -> l2
     | (sa, sb, lst)::t ->
       case findAssociated(sb, findAllAssociated(sa, l2)) of
       | nothing() ->
         combineAssociations_splitGrammar(t, (sa, sb, lst)::l2)
       | just(lst2) ->
         combineAssociations_splitGrammar(t,
            replaceDoubleAssociated((sa, sb), lst ++ lst2, l2))
       end
     end;
}
function replaceDoubleAssociated
[(String, String, [a])] ::= key::(String, String) replace::[a]
                            original::[(String, String, [a])]
{
  return
     case original of
     | [] -> []
     | (sa, sb, current)::tl ->
       if sa == key.1 && sb == key.2
       then (sa, sb, replace)::tl
       else (sa, sb, current)::replaceDoubleAssociated(key, replace, tl)
     end;
}

monoid attribute newInheritedAttrs::[(String, String)] with [], ++;
propagate newInheritedAttrs on ListOfCommands, AnyCommand, TopCommand;

monoid attribute newLocalAttrs::[(String, [(String, String, Type)])]
       with [], combineAssociations(_, _);
propagate newLocalAttrs on ListOfCommands, AnyCommand, TopCommand;

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

monoid attribute newProductions::[(String, String, Type)] with [], ++;
propagate newProductions on ListOfCommands, AnyCommand, TopCommand;


monoid attribute newWPDRelations::[(String, Type, [String])] with [], ++;
propagate newWPDRelations on ListOfCommands, AnyCommand, TopCommand;


monoid attribute newTheorems::[(String, Metaterm)] with [], ++;
propagate newTheorems on ListOfCommands, AnyCommand, TopCommand;


monoid attribute newFunctions::[(String, String, Type)] with [], ++;
propagate newFunctions on ListOfCommands, AnyCommand, TopCommand;





nonterminal ListOfCommands with
   silverContext,
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
      | [(name, arrowType(nameType(nt), _))] when isWpdTypeName(name) ->
        [(name, nameType(encodedToColons(nt)), defs.wpdProdNames)]
        --aren't mutual in components, so can't be in longer list
      | _ -> []
      end;

  top.newFunctions <-
      foldr(\ p::(String, Type) rest::[(String, String, Type)] ->
              if isFun(p.1)
              then let splitName::(String, String) =
                       splitQualifiedName(funToName(p.1))
                   in
                     (splitName.2, splitName.1, p.2)::rest
                   end
              else rest,
            [], preds);
}


aspect production typeDeclaration
top::TopCommand ::= names::[String] ty::Type
{
  top.newProductions <-
      if tyIsNonterminal(ty.resultType)
      then map(\ s::String ->
                 let splitName::(String, String) =
                     splitQualifiedName(prodToName(s))
                 in
                   (splitName.2, splitName.1, ty.colonType)
                 end,
               names)
      else [];

  local attrTy::Type =
        case ty of
        | arrowType(_, arrowType(_, arrowType(functorType(_, attrty), _))) ->
          new(attrty)
        | _ -> error("Access relations must have types of a certain form")
        end;

  top.newAttrs <-
      foldr(\ s::String rest::[(String, String)] ->
              if isAccessRelation(s)
              then let splitName::(String, String) =
                       splitQualifiedName(accessRelationToAttr(s))
                   in
                     (splitName.2, splitName.1)::rest
                   end
              else rest,
            [], names);

  top.newAttrOccurrences <-
      --combining occurrence information for same attr happens by monoid join function
      foldr(\ s::String rest::[(String, String, [(Type, Type)])] ->
              if isAccessRelation(s) &&
                 accessRelationToAttr(s) != "forward"
              then let splitName::(String, String) =
                       splitQualifiedName(accessRelationToAttr(s))
                   in
                     (splitName.2, splitName.1,
                      [(nameType(accessRelationToType(s)),
                        new(attrTy))])::rest
                   end
              else rest,
            [], names);

  top.newInheritedAttrs <-
      foldr(\ s::String rest::[(String, String)] ->
              if endsWith("$_is_inherited", s)
              then let name::String =
                       substring(1, lastIndexOf("$", s), s)
                   in
                   let splitName::(String, String) =
                       splitQualifiedName(encodedToColons(name))
                   in
                     (splitName.2, splitName.1)::rest
                   end end
              else rest,
            [], names);

  top.newLocalAttrs <-
      foldr(\ s::String rest::[(String, [(String, String, Type)])] ->
              if isLocalAccessRelation(s)
              then let prod::String = localAccessToProd(s)
                   in
                   let splitName::(String, String) =
                       splitQualifiedName(prod)
                   in
                     (localAccessToAttr(s),
                      [(splitName.2, splitName.1,
                       case attrTy of
                       | functorType(functorType(nameType("$pair"), ntTy), _)
                         when tyIsNonterminal(ntTy) ->
                         ntTy.colonType
                       | ty -> ty.colonType
                       end)])::rest
                   end end
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

