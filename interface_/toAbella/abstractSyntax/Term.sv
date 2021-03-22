grammar interface_:toAbella:abstractSyntax;


attribute
   translation<Metaterm>, newPremises,
   boundVars, boundVarsOut, attrOccurrences,
   findNameType, foundNameType,
   usedNames,
   replaceName, replaceTerm, replaced,
   removeWPDTree, removedWPD,
   errors
occurs on Metaterm;

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
      | attrAccessTerm(_, _) -> trueMetaterm()
      | _ -> termMetaterm(t.translation, r)
      end;

  t.boundVars = top.boundVars;
  top.boundVarsOut = t.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.usedNames = t.usedNames;

  top.removedWPD = top;
}


aspect production trueMetaterm
top::Metaterm ::=
{
  top.translation = trueMetaterm();

  top.boundVarsOut = top.boundVars;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.usedNames = [];

  top.removedWPD = top;
}


aspect production falseMetaterm
top::Metaterm ::=
{
  top.translation = falseMetaterm();

  top.boundVarsOut = top.boundVars;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.usedNames = [];

  top.removedWPD = top;
}


aspect production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.translation = eqMetaterm(t1.translation, t2.translation);

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  top.boundVarsOut = t2.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.usedNames = t1.usedNames ++ t2.usedNames;

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

  top.usedNames = t1.usedNames ++ t2.usedNames;

  top.removedWPD =
      case t1 of
      | termMetaterm(applicationTerm(nameTerm(wpdRel, _),
                     consTermList(nameTerm(tree, _), _)), _)
           when tree == treeToStructureName(tree) &&
                startsWith("$wpd_nt_", wpdRel) -> t2
      | _ -> impliesMetaterm(t1, t2.removedWPD)
      end;
}


aspect production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.translation = orMetaterm(t1.translation, t2.translation);

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  top.boundVarsOut = t2.boundVarsOut;

  top.foundNameType = left("Did not find name " ++ top.findNameType);

  top.usedNames = t1.usedNames ++ t2.usedNames;

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

  top.usedNames = t1.usedNames ++ t2.usedNames;

  top.removedWPD = top;
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

  --Want ALL names which occur, even if only in bindings
  top.usedNames = map(fst, bindings) ++ body.usedNames;

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

  top.usedNames = t1.usedNames ++ t2.usedNames ++ result.usedNames;

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

  top.usedNames = t1.usedNames ++ t2.usedNames ++ result.usedNames;

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

  top.usedNames = t1.usedNames ++ t2.usedNames ++ result.usedNames;

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

  top.usedNames = t1.usedNames ++ t2.usedNames ++ result.usedNames;

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

  top.usedNames = t1.usedNames ++ t2.usedNames ++ result.usedNames;

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

  top.usedNames = t.usedNames ++ result.usedNames;

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

  top.usedNames = t1.usedNames ++ t2.usedNames ++ result.usedNames;

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

  top.usedNames = t1.usedNames ++ t2.usedNames ++ result.usedNames;

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

  top.usedNames = t1.usedNames ++ t2.usedNames ++ result.usedNames;

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

  top.usedNames = t1.usedNames ++ t2.usedNames ++ result.usedNames;

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

  top.usedNames = t1.usedNames ++ t2.usedNames ++ result.usedNames;

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

  top.usedNames = t1.usedNames ++ t2.usedNames ++ result.usedNames;

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

  top.usedNames = t1.usedNames ++ t2.usedNames ++ result.usedNames;

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

  top.usedNames = t.usedNames ++ result.usedNames;

  top.removedWPD = top;
}





attribute
   translation<Term>, newPremises,
   boundVars, boundVarsOut, attrOccurrences,
   usedNames,
   replaceName, replaceTerm, replaced,
   errors
occurs on Term;

aspect production applicationTerm
top::Term ::= f::Term args::TermList
{
  top.translation = applicationTerm(f.translation, args.translation);

  f.boundVars = top.boundVars;
  args.boundVars = f.boundVarsOut;
  top.boundVarsOut = args.boundVarsOut;

  top.usedNames = f.usedNames ++ args.usedNames;
}


aspect production nameTerm
top::Term ::= name::String ty::Maybe<Type>
{
  top.translation = nameTerm(name, ty);

  top.boundVarsOut = top.boundVars;

  {-
    I don't think we need to check if this name exists because we
    aren't changing this name into a tree.  We might need to do
    something for typing.
  -}

  top.usedNames = [name];

  top.replaced =
      if top.replaceName == name
      then top.replaceTerm
      else top;
}


aspect production consTerm
top::Term ::= t1::Term t2::Term
{
  top.translation = consTerm(t1.translation, t2.translation);

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  top.boundVarsOut = t2.boundVarsOut;

  top.usedNames = t1.usedNames ++ t2.usedNames;
}


aspect production nilTerm
top::Term ::=
{
  top.translation = nilTerm();

  top.boundVarsOut = top.boundVars;

  top.usedNames = [];
}


aspect production underscoreTerm
top::Term ::= ty::Maybe<Type>
{
  top.translation = underscoreTerm(ty);

  top.boundVarsOut = top.boundVars;

  top.usedNames = [];
}


aspect production attrAccessTerm
top::Term ::= treename::String attr::String
{
  top.translation = nameTerm(accessToAccessName(treename, attr), nothing());
  top.newPremises := [attrAccessNewPremise(treename, attr), wpdNewPremise(treename)];

  local occursOnTypes::[Type] =
        case findAssociated(attr, top.attrOccurrences) of
        | just(tys) -> tys
        | nothing() -> [] --unknown attribute
        end;
  local possibleTys::[Type] =
        case findAssociatedScopes(treename, top.boundVars) of
        | just(just(l)) -> intersectBy(tysEqual, occursOnTypes, l)
        | just(nothing()) -> occursOnTypes
        | _ -> error("Should not access local possibleTys if there are errors (attrAccessTerm)")
        end;

  top.boundVarsOut = replaceAssociatedScopes(treename, just(possibleTys), top.boundVars);

  top.errors <-
      --check whether the attribute exists
      case findAssociated(attr, top.attrOccurrences) of
      | just(tys) -> []
      | nothing() -> [errorMsg("Unknown attribute " ++ attr)]
      end ++
      --check whether the tree exists
      case findAssociatedScopes(treename, top.boundVars) of
      | nothing() -> [errorMsg("Unbound name " ++ treename)]
      | _ -> []
      end ++
      --check attribute occurrence of trees of type t
      --maybe this should go on the new premise production
      case findAssociated(attr, top.attrOccurrences),
           findAssociatedScopes(treename, top.boundVars) of
      | just(atys), just(just(ttys)) ->
        if null(intersectBy(tysEqual, atys, ttys))
        then [errorMsg("Attribute " ++ attr ++ " does not occur on " ++ treename)]
        else []
      | _, _ -> []
      end;

  top.usedNames = [treename];
}


aspect production intTerm
top::Term ::= i::Integer
{
  top.translation = integerToIntegerTerm(i);

  top.boundVarsOut = top.boundVars;

  top.usedNames = [];
}


aspect production stringTerm
top::Term ::= contents::String
{
  local charOrdinals::[Integer] = stringToChars(contents);
  local charConstants::[String] = map(ordinalToCharConstructor, charOrdinals);
  local charTerms::[Term] = map(nameTerm(_, nothing()), charConstants);
  top.translation = foldl(consTerm, nilTerm(), charTerms);

  top.boundVarsOut = top.boundVars;

  top.usedNames = [];
}


aspect production trueTerm
top::Term ::=
{
  top.translation = nameTerm(trueName, nothing());

  top.boundVarsOut = top.boundVars;

  top.usedNames = [];
}


aspect production falseTerm
top::Term ::=
{
  top.translation = nameTerm(falseName, nothing());

  top.boundVarsOut = top.boundVars;

  top.usedNames = [];
}


aspect production charTerm
top::Term ::= c::String
{
  top.translation = error("Should not have charTerm in toAbella");

  top.boundVarsOut = error("Should not have charTerm in toAbella");

  top.usedNames = [];
}


aspect production pairTerm
top::Term ::= contents::PairContents
{
  top.translation = contents.translation;

  contents.boundVars = top.boundVars;
  top.boundVarsOut = contents.boundVarsOut;

  top.usedNames = contents.usedNames;
}


aspect production listTerm
top::Term ::= contents::ListContents
{
  top.translation = contents.translation;

  contents.boundVars = top.boundVars;
  top.boundVarsOut = contents.boundVarsOut;

  top.usedNames = contents.usedNames;
}





attribute
   translation<Term>, newPremises,
   boundVars, boundVarsOut, attrOccurrences,
   usedNames,
   replaceName, replaceTerm, replaced,
   errors
occurs on ListContents;

aspect production emptyListContents
top::ListContents ::=
{
  top.translation = nilTerm();

  top.boundVarsOut = top.boundVars;

  top.usedNames = [];
}


aspect production addListContents
top::ListContents ::= hd::Term tl::ListContents
{
  top.translation = consTerm(hd.translation, tl.translation);

  hd.boundVars = top.boundVars;
  tl.boundVars = hd.boundVarsOut;
  top.boundVarsOut = tl.boundVarsOut;

  top.usedNames = hd.usedNames ++ tl.usedNames;
}





attribute
   translation<Term>, newPremises,
   boundVars, boundVarsOut, attrOccurrences,
   usedNames,
   replaceName, replaceTerm, replaced,
   errors
occurs on PairContents;

aspect production singlePairContents
top::PairContents ::= t::Term
{
  top.translation = t.translation;

  t.boundVars = top.boundVars;
  top.boundVarsOut = t.boundVarsOut;

  top.usedNames = t.usedNames;
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

  top.usedNames = t.usedNames ++ rest.usedNames;
}





attribute
   translation<TermList>, newPremises,
   boundVars, boundVarsOut, attrOccurrences,
   usedNames,
   replaceName, replaceTerm, replaced,
   errors
occurs on TermList;

aspect production singleTermList
top::TermList ::= t::Term
{
  top.translation = singleTermList(t.translation);

  t.boundVars = top.boundVars;
  top.boundVarsOut = t.boundVarsOut;

  top.usedNames = t.usedNames;
}


aspect production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.translation = consTermList(t.translation, rest.translation);

  t.boundVars = top.boundVars;
  rest.boundVars = t.boundVarsOut;
  top.boundVarsOut = rest.boundVarsOut;

  top.usedNames = t.usedNames ++ rest.usedNames;
}

