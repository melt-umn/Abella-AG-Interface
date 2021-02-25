grammar interface_:toAbella:abstractSyntax;


attribute
   translation<Metaterm>, newPremises,
   boundVars, boundVarsOut, attrOccurrences,
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
}


aspect production trueMetaterm
top::Metaterm ::=
{
  top.translation = trueMetaterm();

  top.boundVarsOut = top.boundVars;
}


aspect production falseMetaterm
top::Metaterm ::=
{
  top.translation = falseMetaterm();

  top.boundVarsOut = top.boundVars;
}


aspect production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.translation = eqMetaterm(t1.translation, t2.translation);

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  top.boundVarsOut = t2.boundVarsOut;
}


aspect production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.translation = impliesMetaterm(t1.translation, t2.translation);

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  top.boundVarsOut = t2.boundVarsOut;
}


aspect production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.translation = orMetaterm(t1.translation, t2.translation);

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  top.boundVarsOut = t2.boundVarsOut;
}


aspect production andMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.translation = andMetaterm(t1.translation, t2.translation);

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  top.boundVarsOut = t2.boundVarsOut;
}


aspect production bindingMetaterm
top::Metaterm ::= b::Binder bindings::[Pair<String Maybe<Type>>] body::Metaterm
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
                 eqTest = error("Should not require eqTest");},
              noDupPremises)
        end;
  local premisesHere::[Decorated NewPremise] =
        filter((.addPremiseHere), decPremises);
  local newNames::[Pair<String Maybe<Type>>] = concat(map((.newBindingNames), premisesHere));
  local removeNames::[String] = concat(map((.removeBindingNames), premisesHere));
  local transNames::[Pair<String Maybe<Type>>] =
        removeAllBy(\ p::Pair<String Maybe<Type>> name::Pair<String Maybe<Type>> ->
                      case p, name of | pair(a, _), pair(n, _) -> a == n end,
                    map(pair(_, nothing()), removeNames), bindings) ++ newNames;
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

  top.errors :=
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
}





attribute
   translation<Term>, newPremises,
   boundVars, boundVarsOut, attrOccurrences,
   errors
occurs on Term;

aspect production applicationTerm
top::Term ::= f::Term args::TermList
{
  top.translation = applicationTerm(f.translation, args.translation);

  f.boundVars = top.boundVars;
  args.boundVars = f.boundVarsOut;
  top.boundVarsOut = args.boundVarsOut;
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
}


aspect production consTerm
top::Term ::= t1::Term t2::Term
{
  top.translation = consTerm(t1.translation, t2.translation);

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  top.boundVarsOut = t2.boundVarsOut;
}


aspect production nilTerm
top::Term ::=
{
  top.translation = nilTerm();

  top.boundVarsOut = top.boundVars;
}


aspect production underscoreTerm
top::Term ::= ty::Maybe<Type>
{
  top.translation = underscoreTerm(ty);

  top.boundVarsOut = top.boundVars;
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
        end;

  top.boundVarsOut = replaceAssociatedScopes(treename, just(possibleTys), top.boundVars);

  top.errors :=
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
}


aspect production intTerm
top::Term ::= i::Integer
{
  top.translation = integerToIntegerTerm(i);

  top.boundVarsOut = top.boundVars;
}


aspect production stringTerm
top::Term ::= contents::String
{
  local charOrdinals::[Integer] = stringToChars(contents);
  local charConstants::[String] = map(ordinalToCharConstructor, charOrdinals);
  local charTerms::[Term] = map(nameTerm(_, nothing()), charConstants);
  top.translation = foldl(consTerm, nilTerm(), charTerms);

  top.boundVarsOut = top.boundVars;
}


aspect production trueTerm
top::Term ::=
{
  top.translation = nameTerm(trueName, nothing());

  top.boundVarsOut = top.boundVars;
}


aspect production falseTerm
top::Term ::=
{
  top.translation = nameTerm(falseName, nothing());

  top.boundVarsOut = top.boundVars;
}


aspect production charTerm
top::Term ::= c::String
{
  top.translation = error("Should not have charTerm in toAbella");

  top.boundVarsOut = error("Should not have charTerm in toAbella");
}


aspect production listTerm
top::Term ::= contents::ListContents
{
  top.translation = contents.translation;

  contents.boundVars = top.boundVars;
  top.boundVarsOut = contents.boundVarsOut;
}





attribute
   translation<Term>, newPremises,
   boundVars, boundVarsOut, attrOccurrences,
   errors
occurs on ListContents;

aspect production emptyListContents
top::ListContents ::=
{
  top.translation = nilTerm();

  top.boundVarsOut = top.boundVars;
}


aspect production addListContents
top::ListContents ::= hd::Term tl::ListContents
{
  top.translation = consTerm(hd.translation, tl.translation);

  hd.boundVars = top.boundVars;
  tl.boundVars = hd.boundVarsOut;
  top.boundVarsOut = tl.boundVarsOut;
}





attribute
   translation<TermList>, newPremises,
   boundVars, boundVarsOut, attrOccurrences,
   errors
occurs on TermList;

aspect production singleTermList
top::TermList ::= t::Term
{
  top.translation = singleTermList(t.translation);

  t.boundVars = top.boundVars;
  top.boundVarsOut = t.boundVarsOut;
}


aspect production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.translation = consTermList(t.translation, rest.translation);

  t.boundVars = top.boundVars;
  rest.boundVars = t.boundVarsOut;
  top.boundVarsOut = rest.boundVarsOut;
}

