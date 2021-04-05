grammar interface_:toAbella:abstractSyntax;

{-
  We need to be able to work with the axioms behind attribute values,
  such as their uniqueness.  Rather than have the user need to know
  the appropriate axioms behind this, we provide some generic theorems
  which then find the correct axiom to apply for real.
-}


function theorem__attr_unique
Either<String String> ::=
   args::[ApplyArg] withs::[(String, Term)] hyps::[(String, Metaterm)]
{
  --forall Ty (T : Ty) A V1 V2, T.A = V1 -> T.A = V2 -> V1 = V2

  local nameH1::String = head(args).name;
  local findH1::Maybe<Metaterm> =
        if nameH1 == "_"
        then nothing()
        else findAssociated(nameH1, hyps);
  local nameH2::String = head(tail(args)).name;
  local findH2::Maybe<Metaterm> =
        if nameH2 == "_"
        then nothing()
        else findAssociated(nameH2, hyps);

  local attr_ty::Either<String (String, String)> =
        case findH1, findH2 of
        | nothing(), just(termMetaterm(applicationTerm(nameTerm(access, _), _), _))
          when isAccessRelation(access) ->
          right((accessRelationToAttr(access), accessRelationToType(access)))
        | just(termMetaterm(applicationTerm(nameTerm(access, _), _), _)), nothing()
          when isAccessRelation(access) ->
          right((accessRelationToAttr(access), accessRelationToType(access)))
        | just(termMetaterm(applicationTerm(nameTerm(access1, _), _), _)),
          just(termMetaterm(applicationTerm(nameTerm(access2, _), _), _)) ->
          if isAccessRelation(access1) && isAccessRelation(access2) &&
             access1 == access2
          then right((accessRelationToAttr(access1), accessRelationToType(access1)))
          else left("Arguments do not share the same attribute")
        | _, _ -> left("")
        end;

  return
     if length(args) > 2
     then left("Too many arguments to attr_unique")
     else case attr_ty of
          | left("") ->
            case findAssociated("A", withs), findAssociated("Ty", withs) of
            | nothing(), _ ->
              left("Could not find instantiation for attribute")
            | just(nameTerm(attr, _)), just(nameTerm(ty, _)) when startsWith("nt_", ty)->
              right(accessUniqueThm(attr, ty))
            | _, _ ->
              left("Could not find type of tree")
            end
          | right((attr, ty)) ->
            right(accessUniqueThm(attr, ty))
          | left(err) -> left(err)
          end;
}


function theorem__attr_is
Either<String ProofCommand> ::=
   h::HHint depth::Maybe<Integer> args::[ApplyArg]
   withs::[(String, Term)] hyps::[(String, Metaterm)]
{
  --forall Ty (T : Ty) A V,  T.A = V -> is_<Ty> V

  local nameH::String = head(args).name;
  local findH::Maybe<Metaterm> =
        if nameH == "_"
        then nothing()
        else findAssociated(nameH, hyps);

  local attr_ty::Maybe<(String, String)> =
        case findH of
        | just(termMetaterm(applicationTerm(nameTerm(access, _), _), _))
          when isAccessRelation(access) ->
          just((accessRelationToAttr(access), accessRelationToType(access)))
        | _ -> nothing()
        end;
  local cleanedWiths::[(String, Term)] =
        filter(\ p::(String, Term) -> p.fst != "A" && p.fst != "Ty",
               withs);

  return
     if length(args) > 1
     then left("Too many arguments to attr_is")
     else case attr_ty of
          | nothing() ->
            case findAssociated("A", withs), findAssociated("Ty", withs) of
            | nothing(), _ ->
              left("Could not find instantiation for attribute")
            | just(nameTerm(attr, _)), just(nameTerm(ty, _)) when startsWith("nt_", ty)->
              right(applyTactic(h, depth,
                     clearable(false, accessIsThm(attr, ty), []),
                     hypApplyArg("_", [])::args, cleanedWiths))
            | _, _ ->
              left("Could not find type of tree")
            end
          | just((attr, ty)) ->
            right(applyTactic(h, depth,
                     clearable(false, accessIsThm(attr, ty), []),
                     hypApplyArg("_", [])::args, cleanedWiths))
          end;
}

