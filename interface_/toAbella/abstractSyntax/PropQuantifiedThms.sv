grammar interface_:toAbella:abstractSyntax;


{-
  We can't quantify over prop in Abella, which means we can't prove
  some theorems which would quantify over subrelations.  Thus we have
  proof schemas which we can use with assertions to apply the theorem
  we want.  These functions build the proof for the theorem as an
  assertion and the apply for it afterwards.
-}


function apply_theorem__is_list_member
Either<String [ProofCommand]> ::=
   h::HHint depth::Maybe<Integer> args::[ApplyArg] withs::[(String, Term)]
   --The hypotheses in the current context
   hyps::[(String, Metaterm)]
   silverContext::Decorated SilverContext
{
  --The appropriate subrelation is either in the first argument with
  --is_list or as an argument under args
  local subrel::Term =
        case args of
        | [arg1, _] ->
          case get_arg_hyp_metaterm(arg1, hyps) of
          | just(mt) ->
            case get_is_list_subrel_metaterm(mt, silverContext) of
            | just(subrel) -> subrel
            | nothing() -> 
              case findAssociated("SubRel", withs) of
              | just(subrel) -> subrel
              | nothing() -> error("No instance for SubRel")
              end
            end
          | nothing() ->
            case findAssociated("SubRel", withs) of
            | just(subrel) -> subrel
            | nothing() -> error("No instance for SubRel")
            end
          end
        | _ -> error("Wrong number of args to is_list_member")
        end;

  local errorMsg::Maybe<String> =
        case args of
        | [arg1, _] ->
          case get_arg_hyp_metaterm(arg1, hyps) of
          | just(mt) ->
            case get_is_list_subrel_metaterm(mt, silverContext) of
            | just(subrel) -> nothing()
            | nothing() -> 
              case findAssociated("SubRel", withs) of
              | just(subrel) -> nothing()
              | nothing() ->
                just("Could not find an instantiation for SubRel in is_list_member")
              end
            end
          | nothing() ->
            if arg1.name == "_"
            then case findAssociated("SubRel", withs) of
                 | just(subrel) -> nothing()
                 | nothing() ->
                   just("Could not find an instantiation for SubRel in is_list_member")
                 end
            else just("Could not find hypothesis or lemma " ++ arg1.name)
          end
        | _ -> just("is_list_member expects 2 arguments but has " ++
                    toString(length(args)))
        end;

  local prfName::([ProofCommand], String) =
        theorem__is_list_member(subrel);

  return
     case errorMsg of
     | just(str) -> left(str)
     | nothing() ->
       right(prfName.1 ++
             [applyTactic(h, depth, clearable(false, prfName.2, []), args,
                 --SubRel isn't valid for this assertion
                 filter(\ p::(String, Term) -> p.fst != "SubRel", withs))])
     end;
}


function backchain_theorem__is_list_member
Either<String [ProofCommand]> ::=
   depth::Maybe<Integer> withs::[(String, Term)] conclusion::Metaterm
   silverContext::Decorated SilverContext
{
  local subrel::Term =
        case findAssociated("SubRel", withs) of
        | just(subrel) -> subrel
        | nothing() ->
          case conclusion of
          | termMetaterm(applicationTerm(subrel, _), _) -> subrel
          | _ -> error("No instance for subrel")
          end
        end;

  local errorMsg::Maybe<String> =
        case conclusion of
        | termMetaterm(applicationTerm(subrel, _), _) -> nothing()
        | _ ->
          just("Unification failure:  Conclusion does not match " ++
               "theorem conclusion")
        end;

  local prfName::([ProofCommand], String) =
        theorem__is_list_member(subrel);

  return
     case errorMsg of
     | just(str) -> left(str)
     | nothing() ->
       right(prfName.1 ++
             [backchainTactic(depth, clearable(false, prfName.2, []),
                 --SubRel isn't valid for this assertion
                 filter(\ p::(String, Term) -> p.fst != "SubRel", withs))])
     end;
}


function theorem__is_list_member
([ProofCommand], String) ::= subrel::Term
{
  --forall L E, is_list subrel L -> member E L -> subrel E

  local name_Assert::String = "$Assert_" ++ toString(genInt());
  local name_IH::String = "$IH_" ++ toString(genInt());
  local name_H1::String = "$H1_" ++ toString(genInt());
  local name_H2::String = "$H2_" ++ toString(genInt());
  local name_H3::String = "$H3_" ++ toString(genInt());
  local name_H4::String = "$H4_" ++ toString(genInt());

  local theoremStmt::Metaterm =
        --forall L E,
        bindingMetaterm(
           forallBinder(), [("L", nothing()), ("E", nothing())],
        --is_list subrel L ->
        impliesMetaterm(
           termMetaterm(
              buildApplication(nameTerm("is_list", nothing()),
                               [subrel, nameTerm("L", nothing())]),
              emptyRestriction()),
        --member E L
        impliesMetaterm(
           termMetaterm(
              buildApplication(nameTerm("member", nothing()),
                               [nameTerm("E", nothing()),
                                nameTerm("L", nothing())]),
              emptyRestriction()),
        --subrel E
        termMetaterm(
           buildApplication(subrel, [nameTerm("E", nothing())]),
           emptyRestriction()))));
  local proof::[ProofCommand] =
     [
       assertTactic(nameHint(name_Assert), nothing(), theoremStmt),
       --Begin proof of assertion
         inductionTactic(nameHint(name_IH), [1]),
         introsTactic([name_H1, name_H2]),
         caseTactic(nameHint(name_H3), name_H1, false),
         --Subgoal 1
         caseTactic(noHint(), name_H2, false),
         --Subgoal 2
         caseTactic(nameHint(name_H4), name_H2, false),
           --Subgoal 2.1
           searchTactic(),
           --Subgoal 2.2
           backchainTactic(nothing(), clearable(false, name_IH, []), [])
     ];

  return (proof, name_Assert);
}




function apply_theorem__is_list_append
Either<String [ProofCommand]> ::=
   h::HHint depth::Maybe<Integer> args::[ApplyArg] withs::[(String, Term)]
   --The hypotheses in the current context
   hyps::[(String, Metaterm)]
   silverContext::Decorated SilverContext
{

  --The appropriate subrelation is either in the first argument with
  --is_list or as an argument under args
  local subrel::Term =
        case args of
        | [arg1, arg2, _] ->
          --We want to get subrel either from an is_list hypothesis or the withs (SubRel = subrel)
          case get_arg_hyp_metaterm(arg1, hyps), get_arg_hyp_metaterm(arg2, hyps),
               findAssociated("SubRel", withs) of
          | _, _, just(subrel) -> subrel
          | just(mt), _, _
            when get_is_list_subrel_metaterm(mt, silverContext) matches
                 just(subrel) -> subrel
          | _, just(mt), _
            when get_is_list_subrel_metaterm(mt, silverContext) matches
                 just(subrel) -> subrel
          | _, _, _ -> error("Should not access this")
          end
        | _ -> error("Wrong number of args to is_list_append")
        end;

  local errorMsg::Maybe<String> =
        case args of
        | [arg1, arg2, _] ->
          case get_arg_hyp_metaterm(arg1, hyps), get_arg_hyp_metaterm(arg2, hyps),
               findAssociated("SubRel", withs) of
          | _, _, just(subrel) -> nothing()
          | just(mt), _, _
            when get_is_list_subrel_metaterm(mt, silverContext) matches
                 just(subrel) -> nothing()
          | _, just(mt), _
            when get_is_list_subrel_metaterm(mt, silverContext) matches
                 just(subrel) -> nothing()
          | nothing(), _, _ when arg1.name != "_" ->
            just("Could not find hypothesis or lemma " ++ arg1.name)
          | _, nothing(), _ when arg1.name != "_" ->
            just("Could not find hypothesis or lemma " ++ arg2.name)
          | _, _, _ ->
            just("Could not find an instantiation for SubRel in is_list_append")
          end
        | _ -> just("is_list_append expects 2 arguments but was given " ++
                    toString(length(args)))
        end;

  local prfName::([ProofCommand], String) =
        theorem__is_list_append(subrel);

  return
     case errorMsg of
     | just(str) -> left(str)
     | nothing() ->
       right(prfName.1 ++
             [applyTactic(h, depth, clearable(false, prfName.2, []), args,
                 --SubRel isn't valid for this assertion
                 filter(\ p::(String, Term) -> p.fst != "SubRel", withs))])
     end;
}


function backchain_theorem__is_list_append
Either<String [ProofCommand]> ::=
   depth::Maybe<Integer> withs::[(String, Term)] conclusion::Metaterm
   silverContext::Decorated SilverContext
{
  local subrel::Term =
        case lookup("SubRel", withs) of
        | just(subrel) -> subrel
        | nothing() ->
          case get_is_list_subrel_metaterm(conclusion, silverContext) of
          | just(subrel) -> subrel
          | nothing() -> error("Could not find SubRel")
          end
        end;

  local errorMsg::Maybe<String> =
        case lookup("SubRel", withs),
             get_is_list_subrel_metaterm(conclusion, silverContext) of
        | just(s1), just(s2) when s1 != s2 ->
          just("Unification failure for SubRel")
        | nothing(), nothing() ->
          just("Could not identify instantiation for SubRel")
        | _, _ -> nothing()
        end;

  local prfName::([ProofCommand], String) =
        theorem__is_list_append(subrel);

  return
     case errorMsg of
     | just(str) -> left(str)
     | nothing() ->
       right(prfName.1 ++
             [backchainTactic(depth, clearable(false, prfName.2, []),
                 filter(\ p::(String, Term) -> p.1 != "SubRel",
                        withs))])
     end;
}


function theorem__is_list_append
([ProofCommand], String) ::= subrel::Term
{
  --forall L1 L2 L3, is_list subrel L1 -> is_list subrel L2 -> L1 ++ L2 = L3 -> is_list subrel L3
  
  local name_Assert::String = "$Assert_" ++ toString(genInt());
  local name_IH::String = "$IH_" ++ toString(genInt());
  local name_H1::String = "$H1_" ++ toString(genInt()) ++ "a";
  local name_H2::String = "$H2_" ++ toString(genInt()) ++ "b";
  local name_H3::String = "$H3_" ++ toString(genInt()) ++ "c";
  local name_H4::String = "$H4_" ++ toString(genInt()) ++ "d";
  local name_H5::String = "$H5_" ++ toString(genInt()) ++ "e";

  local theoremStmt::Metaterm =
        --forall L1 L2 L3,
        bindingMetaterm(
           forallBinder(), [("L1", nothing()), ("L2", nothing()), ("L3", nothing())],
        --is_list subrel L1 ->
        impliesMetaterm(
           termMetaterm(
              buildApplication(nameTerm("is_list", nothing()),
                               [subrel, nameTerm("L1", nothing())]),
              emptyRestriction()),
        --is_list subrel L2 ->
        impliesMetaterm(
           termMetaterm(
              buildApplication(nameTerm("is_list", nothing()),
                               [subrel, nameTerm("L2", nothing())]),
              emptyRestriction()),
        --$append L1 L2 L3
        impliesMetaterm(
           termMetaterm(
              buildApplication(nameTerm("$append", nothing()),
                               [nameTerm("L1", nothing()),
                                nameTerm("L2", nothing()),
                                nameTerm("L3", nothing())]),
              emptyRestriction()),
        --is_list subrel L3
        termMetaterm(
           buildApplication(nameTerm("is_list", nothing()),
                            [subrel, nameTerm("L3", nothing())]),
           emptyRestriction())))));
  local proof::[ProofCommand] =
     [
       assertTactic(nameHint(name_Assert), nothing(), theoremStmt),
       --Begin proof of assertion
         inductionTactic(nameHint(name_IH), [1]),
         introsTactic([name_H1, name_H2, name_H3]),
         caseTactic(nameHint(name_H4), name_H1, false),
         --Subgoal 1
         caseTactic(noHint(), name_H3, false),
         searchTactic(),
         --Subgoal 2
         caseTactic(nameHint(name_H5), name_H3, false),
         applyTactic(noHint(), nothing(), clearable(false, name_IH, []),
                     [hypApplyArg(name_H4 ++ "1", []), hypApplyArg(name_H2, []),
                      hypApplyArg(name_H5, [])], []),
         searchTactic()
     ];

  return (proof, name_Assert);
}




--Try to find the subrelation term for is_list in a given metaterm
function get_is_list_subrel_metaterm
Maybe<Term> ::= tm::Metaterm silverContext::Decorated SilverContext
{
  return
     case decorate tm with {silverContext = silverContext;} of
     | termMetaterm(applicationTerm(nameTerm("is_list", _),
           consTermList(subrel, _)), _) -> just(subrel)
     | _ -> nothing()
     end;
}





{-
  This is not strictly necessary to handle in the interface in all
  cases.  For types which are not nonterminals, this theorem can be
  written in Abella.  However, since equality of trees (really their
  underlying terms) is handled by a relation which is only shown to
  the user as equality, we need to figure out the correct theorem to
  actually use, which requires this to be a fake theorem.
-}
function apply_theorem__symmetry
Either<String [ProofCommand]> ::=
   h::HHint depth::Maybe<Integer> args::[ApplyArg] withs::[(String, Term)]
   --The hypotheses in the current context
   hyps::[(String, Metaterm)]
   silverContext::Decorated SilverContext
{
  local trms::(Term, Term) =
        case get_arg_hyp_metaterm(head(args), hyps),
             findAssociated("A", withs),
             findAssociated("B", withs) of
          | _, just(atrm), just(btrm) -> (atrm, btrm)
          | just(mtm), _, _ ->
            case decorate mtm with {silverContext = silverContext;} of
            | eqMetaterm(atrm, btrm) ->(new(atrm), new(btrm))
            | termMetaterm(applicationTerm(_,
                 consTermList(atrm, singleTermList(btrm))), _) ->
              (new(atrm), new(btrm))
            | _ -> error("Should not access trms in presence of errors")
            end
          | _, _, _ -> error("Should not access trms in presence of errors")
          end;
  local isNt::Boolean =
        case get_arg_hyp_metaterm(head(args), hyps) of
        | just(mtm) ->
          case decorate mtm with {silverContext = silverContext;} of
          | eqMetaterm(_, _) -> false
          | termMetaterm(applicationTerm(_,
               consTermList(atrm, singleTermList(btrm))), _) -> true
          | _ -> false
          end
        | nothing() ->
          case decorate trms.1 with {silverContext = silverContext;},
               decorate trms.2 with {silverContext = silverContext;} of
          | nameTerm(str, _), _
            when isProd(str) -> true
          | _, nameTerm(str, _)
            when isProd(str) -> true
          | applicationTerm(nameTerm(str, _), _), _
            when isProd(str) -> true
          | _, applicationTerm(nameTerm(str, _), _)
            when isProd(str) -> true
          | _, _ -> false
          end
        | _ -> false
        end;
  local tyNT::Maybe<Type> =
      case get_arg_hyp_metaterm(head(args), hyps) of
      | just(tm) ->
        case decorate tm with {silverContext = silverContext;} of
        | termMetaterm(applicationTerm(nameTerm(str, _), _), _) ->
          just(structureEqToType(str))
        | _ -> nothing()
        end
      | nothing() -> --check trms for productions
        case decorate trms.1 with {silverContext = silverContext;},
             decorate trms.2 with {silverContext = silverContext;} of
        | nameTerm(str, _), _ when isProd(str) ->
          case findProd(str, silverContext) of
          | [(_, ty)] -> just(ty.resultType)
          | _ -> nothing()
          end
        | _, nameTerm(str, _) when isProd(str) ->
          case findProd(str, silverContext) of
          | [(_, ty)] -> just(ty.resultType)
          | _ -> nothing()
          end
        | applicationTerm(nameTerm(str, _), _), _ when isProd(str) ->
          case findProd(str, silverContext) of
          | [(_, ty)] -> just(ty.resultType)
          | _ -> nothing()
          end
        | _, applicationTerm(nameTerm(str, _), _) when isProd(str) ->
          case findProd(str, silverContext) of
          | [(_, ty)] -> just(ty.resultType)
          | _ -> nothing()
          end
        | nameTerm(tr1, _), nameTerm(tr2, _) -> --go search for WPD assumptions
          case find_WPD_nt_hyp(tr1, hyps, silverContext) of
          | just((_, tm)) ->
            case decorate tm with {silverContext = silverContext;} of
            | termMetaterm(applicationTerm(nameTerm(str, _), _), _) -> 
              just(wpdNt_type(str))
            | _ ->nothing()
            end
          | _ -> 
            case find_WPD_nt_hyp(tr1, hyps, silverContext) of
            | just((_, mt)) ->
              case decorate mt with {silverContext = silverContext;} of
              | termMetaterm(applicationTerm(nameTerm(str, _), _), _) -> 
                just(wpdNt_type(str))
              | _ -> nothing()
              end
            | _ -> nothing()
            end
          end
        | _, _ -> nothing()
        end
      | _ -> nothing()
      end;

  local errorMsg::Maybe<String> =
        case args of
        | [arg1] ->
          case get_arg_hyp_metaterm(arg1, hyps),
               findAssociated("A", withs),
               findAssociated("B", withs) of
          | nothing(), _, _ when arg1.name != "_" ->
            just("Could not find hypothesis " ++ arg1.name)
          | nothing(), nothing(), _ ->
            just("Logic variable found at top level")
          | nothing(), _, nothing() ->
            just("Logic variable found at top level")
          | nothing(), just(atrm), just(btrm) -> nothing()
          | just(tm), a, b ->
            case decorate tm with {silverContext = silverContext;}, a, b of
            | eqMetaterm(atrm1, btrm1), just(atrm2), just(btrm2) ->
              if termsEqual(atrm1, atrm2, silverContext)
              then if termsEqual(btrm1, btrm2, silverContext)
                   then nothing()
                   else just("While matching argument #1:\nUnification " ++
                             "failure for argument B")
              else just("While matching argument #1:\nUnification failure for argument A")
            | eqMetaterm(atrm1, btrm1), just(atrm2), nothing() ->
              if termsEqual(atrm1, atrm2, silverContext)
              then nothing()
              else just("While matching argument #1:\nUnification failure for argument A")
            | termMetaterm(applicationTerm(nameTerm(structEq, _),
                 consTermList(atrm1, singleTermList(btrm1))), _),
              just(atrm2), just(btrm2) when isStructureEqName(structEq) ->
              if termsEqual(atrm1, atrm2, silverContext)
              then if termsEqual(btrm1, btrm2, silverContext)
                   then nothing()
                   else just("While matching argument #1:\nUnification " ++
                             "failure for argument B")
              else just("While matching argument #1:\nUnification failure for argument A")
            | eqMetaterm(atrm1, btrm1), nothing(), just(btrm2) ->
              if termsEqual(btrm1, btrm2, silverContext)
              then nothing()
              else just("While matching argument #1:\nUnification failure for argument B")
            | eqMetaterm(atrm1, btrm1), nothing(), nothing() ->
              nothing()
            | termMetaterm(applicationTerm(nameTerm(structEq, _),
                 consTermList(atrm1, singleTermList(btrm1))), _),
              just(atrm2), nothing() when isStructureEqName(structEq) ->
              if termsEqual(atrm1, atrm2, silverContext)
              then nothing()
              else just("While matching argument #1:\nUnification failure for argument A")
            | termMetaterm(applicationTerm(nameTerm(structEq, _),
                 consTermList(atrm1, singleTermList(btrm1))), _),
              nothing(), just(btrm2) when isStructureEqName(structEq) ->
              if termsEqual(btrm1, btrm2, silverContext)
              then nothing()
              else just("While matching argument #1:\nUnification failure for argument B")
            | termMetaterm(applicationTerm(nameTerm(structEq, _),
                 consTermList(atrm1, singleTermList(btrm1))), _),
              nothing(), nothing() when isStructureEqName(structEq) ->
              nothing()
            | _, _, _ -> just("While matching argument #1:\nUnification failure")
            end
          end
        | _ -> just("symmetry expects 1 argument but was given " ++
                    toString(length(args)))
        end;

  local prfNames::([ProofCommand], String, String, String) =
        theorem__symmetry(isNt, tyNT);

  return
     case errorMsg of
     | just(str) -> left(str)
     | nothing() ->
       if (isNt && tyNT.isJust) || !isNt
       then right(prfNames.1 ++
                  [applyTactic(h, depth,
                      clearable(false, prfNames.2, []), args,
                      map(\ p::(String, Term) ->
                            if p.1 == "A" then (prfNames.3, p.2)
                            else if p.1 == "B" then (prfNames.4, p.2)
                            else p, withs))])
       else left("Could not determine tree type for symmetry")
     end;
}


function backchain_theorem__symmetry
Either<String [ProofCommand]> ::=
   depth::Maybe<Integer> withs::[(String, Term)] conclusion::Metaterm
   silverContext::Decorated SilverContext
{
  local trms::(Term, Term) =
        case conclusion of
        | eqMetaterm(btm, atm) -> (atm, btm)
        | termMetaterm(applicationTerm(nameTerm(rel, _), args), _)
          when isStructureEqName(rel) ->
          (head(tail(args.argList)), head(args.argList))
        | _ -> error("Bad conclusion")
        end;

  local isNT::Boolean =
        case conclusion of
        | eqMetaterm(_, _) -> false
        | _ -> true
        end;

  local tyNT::Maybe<Type> =
        case conclusion of
        | termMetaterm(applicationTerm(nameTerm(rel, _), _), _)
          when isStructureEqName(rel) ->
          just(structureEqToType(rel))
        | _ -> nothing()
        end;

  local errorMsg::Maybe<String> =
        case conclusion of
        | eqMetaterm(btm, atm) ->
          case lookup("A", withs) of
          | just(tm) when tm != atm ->
            just("Unification failure (clash betwen " ++ tm.pp ++
                 " and " ++ atm.pp ++ ")")
          | _ -> case lookup("B", withs) of
                 | just(tm) when tm != btm ->
                   just("Unification failure (clash betwen " ++
                        tm.pp ++ " and " ++ btm.pp ++ ")")
                 | _ -> nothing()
                 end
          end
        | termMetaterm(applicationTerm(nameTerm(rel, _), _), _)
          when isStructureEqName(rel) ->
          case lookup("A", withs) of
          | just(tm) when tm != trms.1 ->
            just("Unification failure (clash betwen " ++ tm.pp ++
                 " and " ++ trms.1.pp ++ ")")
          | _ -> case lookup("B", withs) of
                 | just(tm) when tm != trms.2 ->
                   just("Unification failure (clash betwen " ++
                        tm.pp ++ " and " ++ trms.2.pp ++ ")")
                 | _ -> nothing()
                 end
          end
        | _ -> just("Unification failure")
        end;

  local prfNames::([ProofCommand], String, String, String) =
        theorem__symmetry(isNT, tyNT);

  return
     case errorMsg of
     | just(str) -> left(str)
     | nothing() ->
       right(prfNames.1 ++
             [backchainTactic(depth, clearable(false, prfNames.2, []),
                 map(\ p::(String, Term) ->
                       if p.1 == "A" then (prfNames.3, p.2)
                       else if p.1 == "B" then (prfNames.4, p.2)
                       else p, withs))])
     end;
}


function theorem__symmetry
--([proof], thm name, arg1 name (replace A), arg2 name (replace B))
([ProofCommand], String, String, String) ::=
   isNt::Boolean tyNT::Maybe<Type>
{
  --Theorem symmetry[A] : forall (A B : A), A = B -> B = A

  local num::String = toString(genInt());
  local name_Assert::String = "$Assert_" ++ num;
  local hyp1::String = "$Hyp_" ++ num;

  return
     if isNt
     then ([], typeToStructureEq_Symm(tyNT.fromJust), "T1", "T2")
     else ([
            assertTactic(
               nameHint(name_Assert), nothing(),
               bindingMetaterm(
                  forallBinder(),
                  [("$A", nothing()), ("$B", nothing())],
                  eqMetaterm(
                     nameTerm("$A", nothing()),
                     nameTerm("$B", nothing())))),
            --prove assertion
            introsTactic([hyp1]),
            caseTactic(noHint(), hyp1, false),
            searchTactic()
           ], name_Assert, "$A", "$B");
}

