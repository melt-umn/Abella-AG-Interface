grammar interface_:toAbella:abstractSyntax;


attribute
   translation<Metaterm>, newPremises,
   boundVars, boundVarsOut, attrOccurrences, finalTys,
   findNameType, foundNameType,
   replaceName, replaceTerm, replaced,
   removeWPDTree, removedWPD,
   implicationPremises, conjunctionSplit,
   errors,
   treeTys,
   knownDecoratedTrees, knownNames,
   currentState
occurs on Metaterm;


aspect default production
top::Metaterm ::=
{
  top.implicationPremises = [];
  top.conjunctionSplit = [top];
}


aspect production termMetaterm
top::Metaterm ::= t::Term r::Restriction
{
  {-
    We use the bare term `t.a` as a metaterm even though it doesn't
    have type `prop` as a way to say that the attribute has a value.
    However, since this isn't a `prop`, we need to get rid of it in
    the translation.  We do this by translating it to `true`.
  -}
  top.translation =
      case t of
      --| attrAccessTerm(_, _) -> trueMetaterm()
      | _ -> termMetaterm(t.translation, r)
      end;

  t.boundVars = top.boundVars;
  top.boundVarsOut = t.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;

  top.treeTys <-
      case t of
      | applicationTerm(nameTerm(f, _),
                        consTermList(nameTerm(tree, _), _)) ->
        if isAccessRelation(f)
        then [(tree, nameType(accessRelationToType(f)))]
        else if isWpdTypeName(f)
        then [(tree, wpdNt_type(f))]
        else if isStructureEqName(f)
        then [(tree, structureEqToType(f))]
        else []
      | applicationTerm(nameTerm(f, _),
                        consTermList(_,
                        singleTermList(nameTerm(tree, _)))) ->
        if isStructureEqName(f)
        then [(tree, structureEqToType(f))]
        else []
      | _ -> []
      end;
}


aspect production trueMetaterm
top::Metaterm ::=
{
  top.translation = trueMetaterm();

  top.boundVarsOut = top.boundVars;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production falseMetaterm
top::Metaterm ::=
{
  top.translation = falseMetaterm();

  top.boundVarsOut = top.boundVars;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.translation =
      case t1.translation, t2.translation of
      | nameTerm(t1n, _), _ when contains(t1n, top.knownTrees) ->
        case findAssociatedScopes(t1n, top.finalTys) of
        | just(just(ty)) ->
          termMetaterm(
             buildApplication(nameTerm(typeToStructureEqName(ty), nothing()),
                              [t1.translation, t2.translation]),
             emptyRestriction())
        | _ -> error("Could not find type for tree " ++ t1n)
        end
      | _, nameTerm(t2n, _) when contains(t2n, top.knownTrees) ->
        case findAssociatedScopes(t2n, top.finalTys) of
        | just(just(ty)) ->
          termMetaterm(
             buildApplication(nameTerm(typeToStructureEqName(ty), nothing()),
                              [t1.translation, t2.translation]),
             emptyRestriction())
        | _ -> error("Could not find type for tree " ++ t2n)
        end
      | _, _ -> eqMetaterm(t1.translation, t2.translation)
      end;


  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  top.boundVarsOut = t2.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.translation = impliesMetaterm(t1.translation, t2.translation);

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  top.boundVarsOut = t2.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD =
      case t1 of
      | termMetaterm(applicationTerm(nameTerm(wpdRel, _),
                     consTermList(nameTerm(tree, _), _)), _)
           when isWpdTypeName(wpdRel) -> t2
      | _ -> impliesMetaterm(t1, t2.removedWPD)
      end;

  top.implicationPremises = [t1] ++ t2.implicationPremises;

  top.conjunctionSplit = map(impliesMetaterm(t1, _), t2.conjunctionSplit);
}


aspect production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.translation = orMetaterm(t1.translation, t2.translation);

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  top.boundVarsOut = t2.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production andMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.translation = andMetaterm(t1.translation, t2.translation);

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  top.boundVarsOut = t2.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;

  top.conjunctionSplit = t1.conjunctionSplit ++ t2.conjunctionSplit;
}


aspect production bindingMetaterm
top::Metaterm ::= b::Binder bindings::[(String, Maybe<Type>)] body::Metaterm
{
  --We want to add things where the relevant variables are bound, so
  --   we need to check that on each of our things to add/change
  local noDupPremises::[NewPremise] =
        nubBy(\ x::NewPremise y::NewPremise ->
                decorate x with {eqTest = y;}.isEq,
              body.newPremises);
  local decPremises::[Decorated NewPremise] =
        case body.boundVarsOut of
        | [] -> error("We lost a scope somewhere (bindingMetaterm production)")
        | currentScope::_ ->
          map(\ x::NewPremise ->
                decorate x with
                {currentNames = fst(splitList(bindings));
                 boundVarsHere = currentScope;
                 knownNames = top.knownNames;
                 eqTest = error("Should not require eqTest");
                },
              noDupPremises)
        end;
  local premisesHere::[Decorated NewPremise] =
        filter((.addPremiseHere), decPremises);
  local newNames::[Pair<String Maybe<Type>>] = concat(map((.newBindingNames), premisesHere));
  local removeNames::[String] = concat(map((.removeBindingNames), premisesHere));
  local cleanedNames::[Pair<String Maybe<Type>>] =
        removeAllBy(\ p::Pair<String Maybe<Type>> name::Pair<String Maybe<Type>> ->
                      case p, name of | pair(a, _), pair(n, _) -> a == n end,
                    map(pair(_, nothing()), removeNames), bindings) ++ newNames;
  local transNames::[Pair<String Maybe<Type>>] =
        map(\ p::Pair<String Maybe<Type>> ->
              (fst(p), case snd(p) of
                       | just(ty) -> just(ty.translation)
                       | nothing() -> nothing()
                       end),
            cleanedNames);
  top.translation =
     bindingMetaterm(b, transNames,
                     foldr(impliesMetaterm(_, _), body.translation,
                     map(\ x::Decorated NewPremise -> x.translation, premisesHere)));
  top.newPremises :=
     map(\ x::Decorated NewPremise -> new(x),
         filter(\ x::Decorated NewPremise -> !x.addPremiseHere, decPremises));

  body.boundVars =
     map(\ p::Pair<String Maybe<Type>> ->
           case p of
           | pair(a, just(b)) -> pair(a, just([b]))
           | pair(a, nothing()) -> pair(a, nothing())
           end, bindings)::top.boundVars;
  top.boundVarsOut =
      case body.boundVarsOut of
      | [] -> error("We lost a scope somewhere (bindingMetaterm production)")
      | _::otherScopes -> otherScopes
      end;

  body.knownDecoratedTrees =
       flatMap((.gatheredDecoratedTrees), decPremises) ++
       body.gatheredDecoratedTrees ++
       foldr(\ p::(String, String, Term)
               rest::[(String, String, Term)] ->
               if containsAssociated(p.1, bindings)
               then rest
               else p::rest,
             [],  top.knownDecoratedTrees);

  body.finalTys =
       map(\ p::(String, Maybe<[Type]>) ->
             case p of
             | (n, nothing()) -> (n, nothing())
             | (n, just([])) -> (n, nothing())
             | (n, just(h::t)) -> (n, just(h))
             end, head(body.boundVarsOut))::top.finalTys;

  top.foundNameType =
      if containsBy(\ p1::(String, Maybe<Type>) p2::(String, Maybe<Type>) ->
                      p1.fst == p2.fst,
                    (top.findNameType, nothing()), bindings)
      then case body.boundVarsOut of
           | [] -> error("We lost a scope somewhere (bindingMetaterm production)")
           | currentScope::_ ->
             case findAssociated(top.findNameType, currentScope) of
             | nothing() -> left("Did not find name " ++ top.findNameType)
             | just(just([ty])) -> right(ty)
             | just(_) -> left("Could not determine type for name " ++ top.findNameType)
             end
           end
      else left("Did not find name " ++ top.findNameType);

  top.replaced =
      if containsBy(\ p1::(String, Maybe<Type>) p2::(String, Maybe<Type>) ->
                      p1.fst == p2.fst, (top.replaceName, nothing()), bindings)
      then top
      else bindingMetaterm(b, bindings, body.replaced);

  top.removedWPD = top;


  top.errors <-
     --check for names bound here with empty lists
     case body.boundVarsOut of
     | [] -> error("We lost a scope somewhere (bindingMetaterm production)")
     | currentScope::_ ->
       foldr(\ p::Pair<String Maybe<[Type]>> errs::[Error] ->
               case p of
               | pair(name, just([])) ->
                 [errorMsg("No possible type for tree " ++ name ++
                           "; check the attributes being accessed on it")]
               | pair(name, just(h::t)) -> []
               | pair(name, nothing()) -> []
                 --We don't need to check for names with no type information;
                 --   Abella will do that
               end,
             [], currentScope)
     end;
  top.errors <-
      foldr(\ p::(String, Maybe<Type>) rest::[Error] ->
              if startsWith("$", p.1)
              then [errorMsg("Identifiers cannot start with \"$\"")] ++ rest
              else rest,
             [], bindings);
  top.errors <-
      foldr(\ p::(String, Maybe<Type>) rest::[Error] ->
              case p.2 of
              | just(ty) -> ty.errors ++ rest
              | nothing() -> rest
              end,
             [], bindings);

  top.implicationPremises =
      case b of
      | forallBinder() -> body.implicationPremises
      | _ -> []
      end;

  top.conjunctionSplit =
      map(bindingMetaterm(b, bindings, _), body.conjunctionSplit);

  top.treeTys :=
      filter(\ p::(String, Type) ->
               !containsAssociated(p.1, bindings),
             body.treeTys);
}


aspect production attrAccessMetaterm
top::Metaterm ::= tree::String attr::String val::Term
{
  top.translation =
      case possibleTys, findAssociated(tree, top.knownDecoratedTrees) of
      | [ty], just((nodeName, _)) ->
        termMetaterm(
           buildApplication(
              nameTerm(accessRelationName(ty, attr), nothing()),
              [nameTerm(tree, nothing()),
               nameTerm(nodeName, nothing()),
               buildApplication(nameTerm(attributeExistsName, nothing()),
                                [val.translation])]),
           emptyRestriction())
      | _, _ ->
        error("Should not access translation in the presence of errors (attrAccessMetaterm)")
      end;
  top.newPremises := [wpdNewPremise(tree)] ++ val.newPremises;

  local occursOnTypes::[Type] =
        case findAssociated(attr, top.attrOccurrences) of
        | just(tys) -> map(fst, tys)
        | nothing() -> [] --unknown attribute
        end;
  local possibleTys::[Type] =
        case findAssociatedScopes(tree, top.boundVars) of
        | just(just(l)) -> intersectBy(tysEqual, occursOnTypes, l)
        | just(nothing()) -> occursOnTypes
        | nothing() -> []
        end;

  val.boundVars = replaceAssociatedScopes(tree, just(possibleTys), top.boundVars);
  top.boundVarsOut = val.boundVarsOut;

  top.errors <-
      --check whether the attribute exists
      case findAssociated(attr, top.attrOccurrences) of
      | just(tys) -> []
      | nothing() -> [errorMsg("Unknown attribute " ++ attr)]
      end ++
      --check whether the tree exists
      case findAssociatedScopes(tree, top.boundVars) of
      | nothing() -> [errorMsg("Unbound name " ++ tree)]
      | _ -> []
      end ++
      --check attribute occurrence of trees of type t
      case findAssociated(attr, top.attrOccurrences),
           possibleTys of
      | just(atys), ttys ->
        if null(ttys)
        then [errorMsg("Attribute " ++ attr ++ " does not occur on " ++ tree)]
        else if length(ttys) > 1
             then [errorMsg("Could not determine type of tree " ++ tree)]
             else []
      | _, _ -> []
      end;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production attrAccessEmptyMetaterm
top::Metaterm ::= tree::String attr::String
{
  top.translation =
      case possibleTys, findAssociated(tree, top.knownDecoratedTrees) of
      | [ty], just((nodeName, _)) ->
        termMetaterm(
           buildApplication(
              nameTerm(accessRelationName(ty, attr), nothing()),
              [nameTerm(tree, nothing()),
               nameTerm(nodeName, nothing()),
               nameTerm(attributeNotExistsName, nothing())]),
           emptyRestriction())
      | _, _ ->
        error("Should not access translation in the presence of errors (attrAccessEmptyMetaterm)")
      end;
  top.newPremises := [wpdNewPremise(tree)];

  local occursOnTypes::[Type] =
        case findAssociated(attr, top.attrOccurrences) of
        | just(tys) -> map(fst, tys)
        | nothing() -> [] --unknown attribute
        end;
  local possibleTys::[Type] =
        case findAssociatedScopes(tree, top.boundVars) of
        | just(just(l)) -> intersectBy(tysEqual, occursOnTypes, l)
        | just(nothing()) -> occursOnTypes
        | nothing() -> []
        end;

  top.boundVarsOut = replaceAssociatedScopes(tree, just(possibleTys), top.boundVars);

  top.errors <-
      --check whether the attribute exists
      case findAssociated(attr, top.attrOccurrences) of
      | just(tys) -> []
      | nothing() -> [errorMsg("Unknown attribute " ++ attr)]
      end ++
      --check whether the tree exists
      case findAssociatedScopes(tree, top.boundVars) of
      | nothing() -> [errorMsg("Unbound name " ++ tree)]
      | _ -> []
      end ++
      --check attribute occurrence of trees of type t
      case findAssociated(attr, top.attrOccurrences),
           possibleTys of
      | just(atys), ttys ->
        if null(ttys)
        then [errorMsg("Attribute " ++ attr ++ " does not occur on " ++ tree)]
        else if length(ttys) > 1
             then [errorMsg("Could not determine type of tree " ++ tree)]
             else []
      | _, _ -> []
      end;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production localAttrAccessMetaterm
top::Metaterm ::= tree::String attr::String val::Term
{
  top.translation = error("Should not access translation on localAttrAccessMetaterm");

  top.removedWPD = top;

  val.boundVars = top.boundVars;
  top.boundVarsOut = val.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);
}

aspect production localAttrAccessEmptyMetaterm
top::Metaterm ::= tree::String attr::String
{
  top.translation = error("Should not access translation on localAttrAccessEmptyMetaterm");

  top.removedWPD = top;

  top.boundVarsOut = top.boundVars;

  top.foundNameType = left("Did not find name " ++ top.findNameType);
}


aspect production plusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.translation =
      termMetaterm(
         buildApplication(nameTerm(integerAdditionName, nothing()),
                          [t1.translation, t2.translation,
                           result.translation]),
         emptyRestriction());

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  result.boundVars = t2.boundVarsOut;
  top.boundVarsOut = result.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production minusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.translation =
      termMetaterm(
         buildApplication(nameTerm(integerSubtractionName, nothing()),
                          [t1.translation, t2.translation,
                           result.translation]),
         emptyRestriction());

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  result.boundVars = t2.boundVarsOut;
  top.boundVarsOut = result.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production multiplyMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.translation =
      termMetaterm(
         buildApplication(nameTerm(integerMultiplicationName, nothing()),
                          [t1.translation, t2.translation,
                           result.translation]),
         emptyRestriction());

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  result.boundVars = t2.boundVarsOut;
  top.boundVarsOut = result.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production divideMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.translation =
      termMetaterm(
         buildApplication(nameTerm(integerDivisionName, nothing()),
                          [t1.translation, t2.translation,
                           result.translation]),
         emptyRestriction());

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  result.boundVars = t2.boundVarsOut;
  top.boundVarsOut = result.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production modulusMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.translation =
      termMetaterm(
         buildApplication(nameTerm(integerModulusName, nothing()),
                          [t1.translation, t2.translation,
                           result.translation]),
         emptyRestriction());

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  result.boundVars = t2.boundVarsOut;
  top.boundVarsOut = result.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production negateMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.translation =
      termMetaterm(
         buildApplication(nameTerm(integerNegateName, nothing()),
                          [t.translation, result.translation]),
         emptyRestriction());

  t.boundVars = top.boundVars;
  result.boundVars = t.boundVarsOut;
  top.boundVarsOut = result.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production lessMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.translation =
      termMetaterm(
         buildApplication(nameTerm(integerLessName, nothing()),
                          [t1.translation, t2.translation,
                           result.translation]),
         emptyRestriction());

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  result.boundVars = t2.boundVarsOut;
  top.boundVarsOut = result.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production lessEqMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.translation =
      termMetaterm(
         buildApplication(nameTerm(integerLessEqName, nothing()),
                          [t1.translation, t2.translation,
                           result.translation]),
         emptyRestriction());

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  result.boundVars = t2.boundVarsOut;
  top.boundVarsOut = result.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production greaterMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.translation =
      termMetaterm(
         buildApplication(nameTerm(integerGreaterName, nothing()),
                          [t1.translation, t2.translation,
                           result.translation]),
         emptyRestriction());

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  result.boundVars = t2.boundVarsOut;
  top.boundVarsOut = result.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production greaterEqMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.translation =
      termMetaterm(
         buildApplication(nameTerm(integerGreaterEqName, nothing()),
                          [t1.translation, t2.translation,
                           result.translation]),
         emptyRestriction());

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  result.boundVars = t2.boundVarsOut;
  top.boundVarsOut = result.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production appendMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.translation =
      termMetaterm(
         buildApplication(nameTerm(appendName, nothing()),
                          [t1.translation, t2.translation,
                           result.translation]),
         emptyRestriction());

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  result.boundVars = t2.boundVarsOut;
  top.boundVarsOut = result.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production orBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.translation =
      termMetaterm(
         buildApplication(nameTerm(orName, nothing()),
                          [t1.translation, t2.translation,
                           result.translation]),
         emptyRestriction());

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  result.boundVars = t2.boundVarsOut;
  top.boundVarsOut = result.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production andBoolMetaterm
top::Metaterm ::= t1::Term t2::Term result::Term
{
  top.translation =
      termMetaterm(
         buildApplication(nameTerm(andName, nothing()),
                          [t1.translation, t2.translation,
                           result.translation]),
         emptyRestriction());

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  result.boundVars = t2.boundVarsOut;
  top.boundVarsOut = result.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production notBoolMetaterm
top::Metaterm ::= t::Term result::Term
{
  top.translation =
      termMetaterm(
         buildApplication(nameTerm(notName, nothing()),
                          [t.translation, result.translation]),
         emptyRestriction());

  t.boundVars = top.boundVars;
  result.boundVars = t.boundVarsOut;
  top.boundVarsOut = result.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}


aspect production funMetaterm
top::Metaterm ::= funName::String args::ParenthesizedArgs result::Term
{
  top.translation =
      termMetaterm(
         buildApplication(
            nameTerm(nameToFun(funName), nothing()),
            case args.translation of
            | just(a) -> a.argList ++ [result.translation]
            | nothing() -> [result.translation]
            end),
         emptyRestriction());

  top.errors <-
      case findAssociated(funName, top.currentState.knownFunctions) of
      | just(ty) ->
        --Subtract 1 because return type is included
        if length(ty.argumentTypes) - 1 == length(args.argList)
        then []
        else [errorMsg("Function " ++ funName ++ " expected " ++
                       toString(length(ty.argumentTypes) - 1) ++
                       " arguments but got " ++
                       toString(length(args.argList)))]
      | nothing() -> [errorMsg("Unknown function " ++ funName)]
      end;

  args.boundVars = top.boundVars;
  result.boundVars = args.boundVarsOut;
  top.boundVarsOut = result.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.removedWPD = top;
}





attribute
   translation<Term>, newPremises,
   boundVars, boundVarsOut, attrOccurrences,
   replaceName, replaceTerm, replaced,
   errors,
   eqTest<Term>, isEq,
   findParentOf, foundParent,
   isProdStructure,
   knownDecoratedTrees, knownNames,
   currentState
occurs on Term;

aspect production applicationTerm
top::Term ::= f::Term args::TermList
{
  top.translation = applicationTerm(f.translation, args.translation);

  f.boundVars = top.boundVars;
  args.boundVars = f.boundVarsOut;
  top.boundVarsOut = args.boundVarsOut;

  top.isEq =
      case top.eqTest of
      | applicationTerm(f2, args2) ->
        decorate f with {eqTest = f2;}.isEq &&
        decorate args with {eqTest = args2;}.isEq
      | _ -> false
      end;

  args.findParentOf = top.findParentOf;
  top.foundParent =
      if args.isArgHere.isJust
      then case f of
           | nameTerm(str, _) -> just((str, args.isArgHere.fromJust))
           | _ -> error("Should not find anything but nameTerm for foundParent")
           end
      else args.foundParent;

  top.isProdStructure =
      case f of
      | nameTerm(prod, _) -> isProd(prod)
      | _ -> false
      end;
}


aspect production nameTerm
top::Term ::= name::String ty::Maybe<Type>
{
  top.translation =
      case ty of
      | just(nameType("string")) ->
        nameTerm(name, just(stringType))
      | _ -> nameTerm(name, ty)
      end;

  top.boundVarsOut = top.boundVars;

  top.errors <-
      if startsWith("$", name)
      then [errorMsg("Identifiers cannot start with \"$\"")]
      else [];

  {-
    I don't think we need to check if this name exists because we
    aren't changing this name into a tree.  We might need to do
    something for typing.
  -}

  top.replaced =
      if top.replaceName == name
      then top.replaceTerm
      else top;

  top.isEq =
      case top.eqTest of
      | nameTerm(name2, _) -> name == name2
      | _ -> false
      end;

  top.foundParent = nothing();

  top.isProdStructure = isProd(name);
}


aspect production consTerm
top::Term ::= t1::Term t2::Term
{
  top.translation = consTerm(t1.translation, t2.translation);

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  top.boundVarsOut = t2.boundVarsOut;

  top.isEq =
      case top.eqTest of
      | consTerm(t1_2, t2_2) ->
        decorate t1 with {eqTest = t1_2;}.isEq &&
        decorate t2 with {eqTest = t2_2;}.isEq
      | _ -> false
      end;

  top.foundParent = nothing();

  top.isProdStructure = false;
}


aspect production nilTerm
top::Term ::=
{
  top.translation = nilTerm();

  top.boundVarsOut = top.boundVars;

  top.isEq =
      case top.eqTest of
      | nilTerm() -> true
      | _ -> false
      end;

  top.foundParent = nothing();

  top.isProdStructure = false;
}


aspect production underscoreTerm
top::Term ::= ty::Maybe<Type>
{
  top.translation = underscoreTerm(ty);

  top.boundVarsOut = top.boundVars;

  top.isEq = true;

  top.foundParent = nothing();

  top.isProdStructure = false;
}


aspect production intTerm
top::Term ::= i::Integer
{
  top.translation = integerToIntegerTerm(i);

  top.boundVarsOut = top.boundVars;

  top.isEq =
      case top.eqTest of
      | intTerm(i2) -> i == i2
      | _ -> false
      end;

  top.foundParent = nothing();

  top.isProdStructure = false;
}


aspect production stringTerm
top::Term ::= contents::String
{
  local charOrdinals::[Integer] = stringToChars(contents);
  local charConstants::[String] = map(ordinalToCharConstructor, charOrdinals);
  local charTerms::[Term] = map(nameTerm(_, nothing()), charConstants);
  top.translation = foldr(consTerm, nilTerm(), charTerms);

  top.boundVarsOut = top.boundVars;

  top.isEq =
      case top.eqTest of
      | stringTerm(contents2) -> contents == contents2
      | _ -> false
      end;

  top.foundParent = nothing();

  top.isProdStructure = false;
}


aspect production trueTerm
top::Term ::=
{
  top.translation = nameTerm(trueName, nothing());

  top.boundVarsOut = top.boundVars;

  top.isEq =
      case top.eqTest of
      | trueTerm() -> true
      | _ -> false
      end;

  top.foundParent = nothing();

  top.isProdStructure = false;
}


aspect production falseTerm
top::Term ::=
{
  top.translation = nameTerm(falseName, nothing());

  top.boundVarsOut = top.boundVars;

  top.isEq =
      case top.eqTest of
      | falseTerm() -> true
      | _ -> false
      end;

  top.foundParent = nothing();

  top.isProdStructure = false;
}


aspect production charTerm
top::Term ::= c::String
{
  top.translation = error("Should not have charTerm in toAbella");

  top.boundVarsOut = error("Should not have charTerm in toAbella");

  top.isEq =
      case top.eqTest of
      | charTerm(c2) -> c == c2
      | _ -> false
      end;

  top.foundParent = nothing();

  top.isProdStructure = false;
}

aspect production prodTerm
top::Term ::= prodName::String args::ParenthesizedArgs
{
  top.translation =
      case args.translation of
      | just(a) ->
        applicationTerm(nameTerm(nameToProd(prodName), nothing()), a)
      | nothing() ->
        nameTerm(nameToProd(prodName), nothing())
      end;

  args.boundVars = top.boundVars;
  top.boundVarsOut = args.boundVarsOut;

  top.isEq =
      case top.eqTest of
      | prodTerm(prod, args2) when prod == prodName ->
        decorate args with {eqTest = args2;}.isEq
      | _ -> false
      end;

  args.findParentOf = top.findParentOf;
  top.foundParent =
      if args.isArgHere.isJust
      then just((nameToProd(prodName), args.isArgHere.fromJust))
      else args.foundParent;

  top.isProdStructure = true;
}


aspect production pairTerm
top::Term ::= contents::PairContents
{
  top.translation = contents.translation;

  contents.boundVars = top.boundVars;
  top.boundVarsOut = contents.boundVarsOut;

  top.isEq =
      case top.eqTest of
      | pairTerm(contents2) ->
        decorate contents with {eqTest = contents2;}.isEq
      | _ -> false
      end;

  top.foundParent = nothing();

  top.isProdStructure = false;
}


aspect production listTerm
top::Term ::= contents::ListContents
{
  top.translation = contents.translation;

  contents.boundVars = top.boundVars;
  top.boundVarsOut = contents.boundVarsOut;

  top.isEq =
      case top.eqTest of
      | listTerm(contents2) ->
        decorate contents with {eqTest = contents2;}.isEq
      | _ -> false
      end;

  top.foundParent = nothing();

  top.isProdStructure = false;
}





attribute
   translation<Term>, newPremises,
   boundVars, boundVarsOut, attrOccurrences,
   replaceName, replaceTerm, replaced,
   errors,
   eqTest<ListContents>, isEq,
   knownDecoratedTrees, knownNames
occurs on ListContents;

aspect production emptyListContents
top::ListContents ::=
{
  top.translation = nilTerm();

  top.boundVarsOut = top.boundVars;

  top.isEq =
      case top.eqTest of
      | emptyListContents() -> true
      | _ -> false
      end;
}


aspect production addListContents
top::ListContents ::= hd::Term tl::ListContents
{
  top.translation = consTerm(hd.translation, tl.translation);

  hd.boundVars = top.boundVars;
  tl.boundVars = hd.boundVarsOut;
  top.boundVarsOut = tl.boundVarsOut;

  top.isEq =
      case top.eqTest of
      | addListContents(hd2, tl2) ->
        decorate hd with {eqTest = hd2;}.isEq &&
        decorate tl with {eqTest = tl2;}.isEq
      | _ -> false
      end;
}





attribute
   translation<Term>, newPremises,
   boundVars, boundVarsOut, attrOccurrences,
   replaceName, replaceTerm, replaced,
   errors,
   eqTest<PairContents>, isEq,
   knownDecoratedTrees, knownNames
occurs on PairContents;

aspect production singlePairContents
top::PairContents ::= t::Term
{
  top.translation = t.translation;

  t.boundVars = top.boundVars;
  top.boundVarsOut = t.boundVarsOut;

  top.isEq =
      case top.eqTest of
      | singlePairContents(t2) ->
        decorate t with {eqTest = t2;}.isEq
      | _ -> false
      end;
}


aspect production addPairContents
top::PairContents ::= t::Term rest::PairContents
{
  top.translation =
      buildApplication(nameTerm(pairConstructorName, nothing()),
                       [t.translation, rest.translation]);

  t.boundVars = top.boundVars;
  rest.boundVars = t.boundVarsOut;
  top.boundVarsOut = rest.boundVarsOut;

  top.isEq =
      case top.eqTest of
      | addPairContents(t2, rest2) ->
        decorate t with {eqTest = t2;}.isEq &&
        decorate rest with {eqTest = rest2;}.isEq
      | _ -> false
      end;
}





attribute
   translation<Maybe<TermList>>, newPremises,
   boundVars, boundVarsOut, attrOccurrences,
   replaceName, replaceTerm, replaced,
   errors,
   eqTest<ParenthesizedArgs>, isEq,
   findParentOf, foundParent, isArgHere,
   knownDecoratedTrees, knownNames
occurs on ParenthesizedArgs;

aspect production emptyParenthesizedArgs
top::ParenthesizedArgs ::=
{
  top.translation = nothing();

  top.boundVarsOut = top.boundVars;

  top.isEq =
      case top.eqTest of
      | emptyParenthesizedArgs() -> true
      | _ -> false
      end;

  top.foundParent = nothing();
  top.isArgHere = nothing();
}


aspect production addParenthesizedArgs
top::ParenthesizedArgs ::= hd::Term tl::ParenthesizedArgs
{
  top.translation =
      case tl.translation of
      | just(tlt) -> just(consTermList(hd.translation, tlt))
      | nothing() -> just(singleTermList(hd.translation))
      end;

  hd.boundVars = top.boundVars;
  tl.boundVars = hd.boundVarsOut;
  top.boundVarsOut = tl.boundVarsOut;

  top.isEq =
      case top.eqTest of
      | addParenthesizedArgs(hd2, tl2) ->
        decorate hd with {eqTest = hd2;}.isEq &&
        decorate tl with {eqTest = tl2;}.isEq
      | _ -> false
      end;

  hd.findParentOf = top.findParentOf;
  tl.findParentOf = top.findParentOf;
  top.foundParent =
      case hd.foundParent of
      | just(_) -> hd.foundParent
      | nothing() -> tl.foundParent
      end;
  top.isArgHere =
      case hd of
      | nameTerm(str, _) when str == top.findParentOf ->
        just(0) --0-based indexing
      | _ -> bind(tl.isArgHere, \x::Integer -> just(x + 1))
      end;
}





attribute
   translation<TermList>, newPremises,
   boundVars, boundVarsOut, attrOccurrences,
   replaceName, replaceTerm, replaced,
   errors,
   eqTest<TermList>, isEq,
   findParentOf, foundParent, isArgHere,
   knownDecoratedTrees
occurs on TermList;

aspect production singleTermList
top::TermList ::= t::Term
{
  top.translation = singleTermList(t.translation);

  t.boundVars = top.boundVars;
  top.boundVarsOut = t.boundVarsOut;

  top.isEq =
      case top.eqTest of
      | singleTermList(t2) ->
        decorate t with {eqTest = t2;}.isEq
      | _ -> false
      end;

  t.findParentOf = top.findParentOf;
  top.foundParent = t.foundParent;
  top.isArgHere =
      case t of
      | nameTerm(str, _) when str == top.findParentOf ->
        just(0) --0-based indexing
      | _ -> nothing()
      end;
}


aspect production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.translation = consTermList(t.translation, rest.translation);

  t.boundVars = top.boundVars;
  rest.boundVars = t.boundVarsOut;
  top.boundVarsOut = rest.boundVarsOut;

  top.isEq =
      case top.eqTest of
      | consTermList(t2, rest2) ->
        decorate t with {eqTest = t2;}.isEq &&
        decorate rest with {eqTest = rest2;}.isEq
      | _ -> false
      end;

  t.findParentOf = top.findParentOf;
  rest.findParentOf = top.findParentOf;
  top.foundParent =
      case t.foundParent of
      | just(_) -> t.foundParent
      | nothing() -> rest.foundParent
      end;
  top.isArgHere =
      case t of
      | nameTerm(str, _) when str == top.findParentOf ->
        just(0) --0-based indexing
      | _ -> bind(rest.isArgHere, \x::Integer -> just(x + 1))
      end;
}



aspect production emptyTermList
top::TermList ::=
{
  top.translation = emptyTermList();

  top.boundVarsOut = top.boundVars;

  top.isEq =
      case top.eqTest of
      | emptyTermList() -> true
      | _ -> false
      end;

  top.foundParent = nothing();
  top.isArgHere = nothing();
}

