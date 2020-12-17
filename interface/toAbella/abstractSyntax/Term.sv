grammar toAbella:abstractSyntax;


nonterminal Metaterm with
   pp,
   translation<Metaterm>, newPremises,
   boundVars, boundVarsOut, attrOccurrences,
   errors;

abstract production termMetaterm
top::Metaterm ::= t::Term r::Restriction
{
  top.pp = t.pp ++ r.pp;

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


abstract production trueMetaterm
top::Metaterm ::=
{
  top.pp = "true";

  top.translation = trueMetaterm();

  top.boundVarsOut = top.boundVars;
}


abstract production falseMetaterm
top::Metaterm ::=
{
  top.pp = "false";

  top.translation = falseMetaterm();

  top.boundVarsOut = top.boundVars;
}


abstract production eqMetaterm
top::Metaterm ::= t1::Term t2::Term
{
  top.pp = t1.pp ++ " = " ++ t2.pp;

  top.translation = eqMetaterm(t1.translation, t2.translation);

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  top.boundVarsOut = t2.boundVarsOut;
}


abstract production impliesMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp = "(" ++ t1.pp ++ ") -> " ++ t2.pp;

  top.translation = impliesMetaterm(t1.translation, t2.translation);

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  top.boundVarsOut = t2.boundVarsOut;
}


abstract production orMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp = "(" ++ t1.pp ++ ") \\/ (" ++ t2.pp ++ ")";

  top.translation = orMetaterm(t1.translation, t2.translation);

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  top.boundVarsOut = t2.boundVarsOut;
}


abstract production andMetaterm
top::Metaterm ::= t1::Metaterm t2::Metaterm
{
  top.pp = "(" ++ t1.pp ++ ") /\\ (" ++ t2.pp ++ ")";

  top.translation = andMetaterm(t1.translation, t2.translation);

  t1.boundVars = top.boundVars;
  t2.boundVars = t1.boundVarsOut;
  top.boundVarsOut = t2.boundVarsOut;
}


abstract production bindingMetaterm
top::Metaterm ::= b::Binder bindings::[Pair<String Maybe<Type>>] body::Metaterm
{
  local bindingsString::String =
     if null(bindings)
     then error("Empty bindings not allowed; production bindingsMetaterm")
     else foldr1(\ a::String b::String -> a ++ " " ++ b,
                 map(\p::Pair<String Maybe<Type>> ->
                     case p of
                     | pair(a, just(ty)) -> "(" ++ a ++ " : " ++ ty.pp ++ ")"
                     | pair(a, nothing()) -> a
                     end, bindings));
  top.pp = b.pp ++ " " ++ bindingsString ++ ", " ++ body.pp;

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
                {currentNames = fst(splitList(bindings)); boundVarsHere = currentScope;},
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
                     foldr(impliesMetaterm(_, _), body,
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





nonterminal Restriction with pp;

abstract production emptyRestriction
top::Restriction ::=
{
  top.pp = "";
}


abstract production starRestriction
top::Restriction ::= n::Integer
{
  top.pp = replicate(n, "*");
}


abstract production atRestriction
top::Restriction ::= n::Integer
{
  top.pp = replicate(n, "@");
}


abstract production plusRestriction
top::Restriction ::= n::Integer
{
  top.pp = replicate(n, "+");
}


abstract production hashRestriction
top::Restriction ::= n::Integer
{
  top.pp = replicate(n, "#");
}





nonterminal Binder with pp;

abstract production forallBinder
top::Binder ::=
{
  top.pp = "forall";
}


abstract production existsBinder
top::Binder ::=
{
  top.pp = "exists";
}


abstract production nablaBinder
top::Binder::=
{
  top.pp = "nabla";
}





nonterminal Term with
   pp,
   translation<Term>, newPremises,
   boundVars, boundVarsOut, attrOccurrences,
   errors;

abstract production applicationTerm
top::Term ::= f::Term args::TermList
{
  top.pp = "(" ++ f.pp ++ ") " ++ args.pp;

  top.translation = applicationTerm(f.translation, args.translation);

  f.boundVars = top.boundVars;
  args.boundVars = f.boundVarsOut;
  top.boundVarsOut = args.boundVarsOut;
}


abstract production nameTerm
top::Term ::= name::String ty::Maybe<Type>
{
  top.pp = case ty of
           | just(t) -> "(" ++ name ++ " : " ++ t.pp ++ ")"
           | nothing() -> name
           end;

  top.translation = nameTerm(name, ty);

  top.boundVarsOut = top.boundVars;

  {-
    I don't think we need to check if this name exists because we
    aren't changing this name into a tree.
  -}
}


abstract production underscoreTerm
top::Term ::= ty::Maybe<Type>
{
  top.pp = case ty of
           | just(t) -> "(_ : " ++ t.pp ++ ")"
           | nothing() -> "_"
           end;

  top.translation = underscoreTerm(ty);

  top.boundVarsOut = top.boundVars;
}


abstract production attrAccessTerm
top::Term ::= treename::String attr::String
{
  top.pp = treename ++ "." ++ attr;

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





nonterminal TermList with
   pp,
   translation<TermList>, newPremises,
   boundVars, boundVarsOut, attrOccurrences,
   errors;

abstract production singleTermList
top::TermList ::= t::Term
{
  top.pp = "(" ++ t.pp ++ ")";

  top.translation = singleTermList(t.translation);
}


abstract production consTermList
top::TermList ::= t::Term rest::TermList
{
  top.pp = "(" ++ t.pp ++ ") " ++ rest.pp;

  top.translation = consTermList(t.translation, rest.translation);
}
