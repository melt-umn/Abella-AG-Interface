grammar interface_:toAbella:abstractSyntax;

{-
  We need to be able to work with the axioms behind attribute values,
  such as their uniqueness.  Rather than have the user need to know
  the appropriate axioms behind this, we provide some generic theorems
  which then find the correct axiom to apply for real.
-}


function apply_theorem__attr_unique
Either<String [ProofCommand]> ::=
   h::HHint depth::Maybe<Integer>
   args::[ApplyArg] withs::[(String, Term)] hyps::[(String, Metaterm)]
   silverContext::Decorated SilverContext
{
  --forall Ty (Tree : Ty) A V1 V2, Tree.A = V1 -> Tree.A = V2 -> V1 = V2

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
        | nothing(), just(mtm) ->
          case decorate mtm with {silverContext = silverContext;} of
          | termMetaterm(applicationTerm(nameTerm(access, _), _), _)
            when isAccessRelation(access) ->
            right((accessRelationToAttr(access), accessRelationToType(access)))
          | _ -> left("")
          end
        | just(mtm), nothing() ->
          case decorate mtm with {silverContext = silverContext;} of
          | termMetaterm(applicationTerm(nameTerm(access, _), _), _)
            when isAccessRelation(access) ->
            right((accessRelationToAttr(access), accessRelationToType(access)))
          | _ -> left("")
          end
        | just(mtm1), just(mtm2) ->
          case decorate mtm1 with {silverContext = silverContext;},
               decorate mtm2 with {silverContext = silverContext;} of
          | termMetaterm(applicationTerm(nameTerm(access1, _), _), _),
            termMetaterm(applicationTerm(nameTerm(access2, _), _), _) ->
            if isAccessRelation(access1) && isAccessRelation(access2) &&
               access1 == access2
            then right((accessRelationToAttr(access1), accessRelationToType(access1)))
            else left("Arguments do not share the same attribute")
          | _, _ -> left("")
          end
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
            | just(tm1), just(tm2) ->
              case decorate tm1 with {silverContext = silverContext;},
                   decorate tm2 with {silverContext = silverContext;} of
              | nameTerm(attr, _), nameTerm(ty, _)
                when nameIsNonterminal(ty)->
                right([applyTactic(h, depth,
                          clearable(false, accessUniqueThm(attr, ty), []),
                          args, filter(\ p::(String, Term) ->
                                         p.1 != "A" && p.1 != "Ty", withs))])
              | _, _ ->
                left("Could not find type of tree")
              end
            | _, _ -> left("Could not find type of tree")
            end
          | right((attr, ty)) ->
            right([applyTactic(h, depth,
                      clearable(false, accessUniqueThm(attr, ty), []),
                      args, filter(\ p::(String, Term) ->
                                     p.1 != "A" && p.1 != "Ty", withs))])
          | left(err) -> left(err)
          end;
}


function backchain_theorem__attr_unique
Either<String [ProofCommand]> ::=
   depth::Maybe<Integer> withs::[(String, Term)] hyps::[(String, Metaterm)]
   silverContext::Decorated SilverContext
{
  --forall Ty (Tree : Ty) A V1 V2, Tree.A = V1 -> Tree.A = V2 -> V1 = V2

  local ty::Either<String String> =
        case lookup("Ty", withs) of
        | just(typ) ->
          case decorate typ with {silverContext = silverContext;} of
          | nameTerm(tyName, _) ->
            case findNonterminal(tyName, silverContext) of
            | [fullTy] -> right(fullTy)
            | [] -> left("Unknown nonterminal type " ++ tyName)
            | l ->
              left("Indeterminate nonterminal type " ++ tyName ++
                   "; could be [" ++ implode(", ", l) ++ "]")
            end
          | _ -> left("Could not find instantiation for Ty")
          end
        | _ ->
          case lookup("T", withs) of
          | just(tm) ->
            case decorate tm with {silverContext = silverContext;} of
            | nameTerm(tree, _) ->
              foldr(\ hyp::(String, Metaterm) rest::Either<String String> ->
                      case rest, decorate hyp.2 with {silverContext = silverContext;} of
                      | right(_), _ -> rest
                      | _, termMetaterm(
                              applicationTerm(nameTerm(rel, _), args), _)
                        when isAccessRelation(rel) ->
                        case args.argList of
                        | tm::_ ->
                          case decorate tm with {silverContext = silverContext;} of
                          | nameTerm(t, _) when t == tree ->
                            right(accessRelationToType(rel))
                          | _ -> rest
                          end
                        | _ -> rest
                        end
                      | _, termMetaterm(
                              applicationTerm(nameTerm(rel, _), args), _)
                        when isWpdTypeName(rel) ->
                        case args.argList of
                        | tm::_ ->
                          case decorate tm with {silverContext = silverContext;} of
                          | nameTerm(t, _) when t == tree ->
                            right(wpdToTypeName(rel))
                          | _ -> rest
                          end
                        | _ -> rest
                        end
                      | _, _ -> rest
                      end,
                    left("Could not find instantiation for Ty"), hyps)
            | _ -> left("Could not find instantiation for Ty")
            end
          | _ -> left("Could not find instantiation for Ty")
          end
        end;
  local attr::Either<String String> =
        case lookup("A", withs), ty of
        | just(t), right(tyName) ->
          case decorate t with {silverContext = silverContext;} of
          | nameTerm(a, _) ->
            case findAttrOccurrences(a, silverContext) of
            | [] -> left("Unknown attribute " ++ a)
            | l -> 
              case filter(\ p::(String, [(Type, Type)]) ->
                            contains(
                               nameType(nameToColonNonterminalName(tyName)),
                               map(fst, p.2)),
                          l) of
              | [] -> left("Attribute " ++ a ++ " does not occur on type " ++ tyName)
              | [(fullA, _)] -> right(fullA)
              | l -> left("Undetirimend attribute " ++ a ++ "; could be [" ++
                          implode(", ", map(fst, l)) ++ "]")
              end
            end
          | _ -> left("Could not find instantiation for attribute")
          end
        | _, _ -> left("Could not find instantiation for attribute")
        end;

  return
     case attr, ty of
     | right(attrName), right(tyName) ->
       right(
          [backchainTactic(depth,
              clearable(false, accessUniqueThm(attrName, tyName), []),
              filter(\ p::(String, Term) -> p.1 != "A" && p.1 != "Ty",
                     withs))])
     | left(s), _ -> left(s)
     | _, left(s) -> left(s)
     end;
}




function apply_theorem__attr_is
Either<String [ProofCommand]> ::=
   h::HHint depth::Maybe<Integer> args::[ApplyArg]
   withs::[(String, Term)] hyps::[(String, Metaterm)]
   silverContext::Decorated SilverContext
{
  --forall Ty (T : Ty) A V,  T.A = V -> is_<Ty> V

  local nameH::String = head(args).name;
  local findH::Maybe<Metaterm> =
        if nameH == "_"
        then nothing()
        else findAssociated(nameH, hyps);

  local attr_ty::Maybe<(String, String)> =
        if findH.isJust
        then case decorate findH.fromJust with
                  {silverContext = silverContext;} of
             | termMetaterm(applicationTerm(nameTerm(access, _), _), _)
               when isAccessRelation(access) ->
               just((accessRelationToAttr(access), accessRelationToType(access)))
             | _ -> nothing()
             end
        else nothing();
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
            | just(tm1), just(tm2) ->
              case decorate tm1 with {silverContext = silverContext;},
                   decorate tm2 with {silverContext = silverContext;} of
              | nameTerm(attr, _), nameTerm(ty, _)
                when nameIsNonterminal(ty)->
                right([applyTactic(h, depth,
                        clearable(false, accessIsThm(attr, ty), []),
                        hypApplyArg("_", [])::args, cleanedWiths)])
              | _, _ ->
                left("Could not find type of tree")
              end
            | _, _ ->
              left("Could not find type of tree")
            end
          | just((attr, ty)) ->
            right([applyTactic(h, depth,
                      clearable(false, accessIsThm(attr, ty), []),
                      hypApplyArg("_", [])::args, cleanedWiths)])
          end;
}


function backchain_theorem__attr_is
Either<String [ProofCommand]> ::=
   depth::Maybe<Integer> withs::[(String, Term)]
   hyps::[(String, Metaterm)] conclusion::Metaterm
   silverContext::Decorated SilverContext
{
  --forall Ty (T : Ty) A V, T.A = V -> is_<Ty> V

  local ty::Either<String String> =
        case lookup("Ty", withs) of
        | just(typ) ->
          case decorate typ with {silverContext = silverContext;} of
          | nameTerm(tyName, _) ->
            case findNonterminal(tyName, silverContext) of
            | [fullTy] -> right(fullTy)
            | [] -> left("Unknown nonterminal type " ++ tyName)
            | l ->
              left("Indeterminate nonterminal type " ++ tyName ++
                   "; could be [" ++ implode(", ", l) ++ "]")
            end
          | _ -> left("Could not find instantiation for Ty")
          end
        | _ ->
          case lookup("T", withs) of
          | just(tm) ->
            case decorate tm with {silverContext = silverContext;} of
            | nameTerm(tree, _) ->
              foldr(\ hyp::(String, Metaterm) rest::Either<String String> ->
                      case rest, decorate hyp.2 with {silverContext = silverContext;} of
                      | right(_), _ -> rest
                      | _, termMetaterm(
                              applicationTerm(nameTerm(rel, _), args), _)
                        when isAccessRelation(rel) ->
                        case args.argList of
                        | tm::_ ->
                          case decorate tm with {silverContext = silverContext;} of
                          | nameTerm(t, _) when t == tree ->
                            right(accessRelationToType(rel))
                          | _ -> rest
                          end
                        | _ -> rest
                        end
                      | _, termMetaterm(
                              applicationTerm(nameTerm(rel, _), args), _)
                        when isWpdTypeName(rel) ->
                        case args.argList of
                        | tm::_ ->
                          case decorate tm with {silverContext = silverContext;} of
                          | nameTerm(t, _) when t == tree ->
                            right(wpdToTypeName(rel))
                          | _ -> rest
                          end
                        | _ -> rest
                        end
                      | _, _ -> rest
                      end,
                    left("Could not find instantiation for Ty"), hyps)
            | _ -> left("Could not find instantiation for Ty")
            end
          | _ -> left("Could not find instantiation for Ty")
          end
        end;
  local attr::Either<String String> =
        case lookup("A", withs), ty of
        | just(t), right(tyName) ->
          case decorate t with {silverContext = silverContext;} of
          | nameTerm(a, _) ->
            case findAttrOccurrences(a, silverContext) of
            | [] -> left("Unknown attribute " ++ a)
            | l -> 
              case filter(\ p::(String, [(Type, Type)]) ->
                            contains(
                               nameType(nameToColonNonterminalName(tyName)),
                               map(fst, p.2)),
                          l) of
              | [] -> left("Attribute " ++ a ++ " does not occur on type " ++ tyName)
              | [(fullA, _)] -> right(fullA)
              | l -> left("Undetirimend attribute " ++ a ++ "; could be [" ++
                          implode(", ", map(fst, l)) ++ "]")
              end
            end
          | _ -> left("Could not find instantiation for attribute")
          end
        | _, _ -> left("Could not find instantiation for attribute")
        end;

  return
     case attr, ty of
     | right(attrName), right(tyName) ->
       right([backchainTactic(depth,
                 clearable(false,
                    accessIsThm(attrName,
                       nameToNonterminalName(tyName)), []),
                 filter(\ p::(String, Term) ->
                          p.1 != "A" && p.1 != "Ty", withs))])
     | left(s), _ -> left(s)
     | _, left(s) -> left(s)
     end;
}

