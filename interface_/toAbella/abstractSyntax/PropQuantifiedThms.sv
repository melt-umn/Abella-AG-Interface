grammar interface_:toAbella:abstractSyntax;


{-
  We can't quantify over prop in Abella, which means we can't prove
  some theorems which would quantify over subrelations.  Thus we have
  proof schemas which we can use with assertions to apply the theorem
  we want.  These functions build the proof for the theorem as an
  assertion and the apply for it afterwards.
-}


function theorem__is_list_member
Either<String [ProofCommand]> ::=
   h::HHint depth::Maybe<Integer> args::[ApplyArg] withs::[(String, Term)]
   --The hypotheses in the current context
   hyps::[(String, Metaterm)]
{
  --forall L E, is_list subrel L -> member E L -> subrel E

  local name_Assert::String = "$Assert_" ++ toString(genInt());
  local name_IH::String = "$IH_" ++ toString(genInt());
  local name_H1::String = "$H1_" ++ toString(genInt());
  local name_H2::String = "$H2_" ++ toString(genInt());
  local name_H3::String = "$H3_" ++ toString(genInt());
  local name_H4::String = "$H4_" ++ toString(genInt());

  --The appropriate subrelation is either in the first argument with
  --is_list or as an argument under args
  local subrel::Term =
        case args of
        | [arg1, _] ->
          case get_arg_hyp_metaterm(arg1, hyps) of
          | just(mt) ->
            case get_is_list_subrel_metaterm(mt) of
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
           backchainTactic(nothing(), clearable(false, name_IH, []), []),
             --applyTactic(noHint(), nothing(), clearable(false, name_IH, []),
             --     [hypApplyArg(name_H1, []), hypApplyArg(name_H4, [])], []),
             --searchTactic(),
       --End assertion proof
       applyTactic(h, depth, clearable(false, name_Assert, []), args,
                   --SubRel isn't valid for this assertion
                   filter(\ p::(String, Term) -> p.fst != "SubRel", withs))
     ];


  local errorMsg::Maybe<String> =
        case args of
        | [arg1, _] ->
          case get_arg_hyp_metaterm(arg1, hyps) of
          | just(mt) ->
            case get_is_list_subrel_metaterm(mt) of
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

  return
     case errorMsg of
     | just(str) -> left(str)
     | nothing() -> right(proof)
     end;
}


function theorem__is_list_append
Either<String [ProofCommand]> ::=
   h::HHint depth::Maybe<Integer> args::[ApplyArg] withs::[(String, Term)]
   --The hypotheses in the current context
   hyps::[(String, Metaterm)]
{
  --forall L E, is_list subrel L -> member E L -> subrel E
  
  local name_Assert::String = "$Assert_" ++ toString(genInt());
  local name_IH::String = "$IH_" ++ toString(genInt());
  local name_H1::String = "$H1_" ++ toString(genInt()) ++ "a";
  local name_H2::String = "$H2_" ++ toString(genInt()) ++ "b";
  local name_H3::String = "$H3_" ++ toString(genInt()) ++ "c";
  local name_H4::String = "$H4_" ++ toString(genInt()) ++ "d";
  local name_H5::String = "$H5_" ++ toString(genInt()) ++ "e";

  --The appropriate subrelation is either in the first argument with
  --is_list or as an argument under args
  local subrel::Term =
        case args of
        | [arg1, arg2, _] ->
          --We want to get subrel either from an is_list hypothesis or the withs (SubRel = subrel)
          case get_arg_hyp_metaterm(arg1, hyps), get_arg_hyp_metaterm(arg2, hyps),
               findAssociated("SubRel", withs) of
          | _, _, just(subrel) -> subrel
          | just(mt), _, _ when get_is_list_subrel_metaterm(mt) matches just(subrel) -> subrel
          | _, just(mt), _ when get_is_list_subrel_metaterm(mt) matches just(subrel) -> subrel
          | _, _, _ -> error("Should not access this")
          end
        | _ -> error("Wrong number of args to is_list_append")
        end;
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
         searchTactic(),
       --End assertion proof
       applyTactic(h, depth, clearable(false, name_Assert, []), args,
                   --SubRel isn't valid for this assertion
                   filter(\ p::(String, Term) -> p.fst != "SubRel", withs))
     ];


  local errorMsg::Maybe<String> =
        case args of
        | [arg1, arg2, _] ->
          case get_arg_hyp_metaterm(arg1, hyps), get_arg_hyp_metaterm(arg2, hyps),
               findAssociated("SubRel", withs) of
          | _, _, just(subrel) -> nothing()
          | just(mt), _, _ when get_is_list_subrel_metaterm(mt) matches just(subrel) -> nothing()
          | _, just(mt), _ when get_is_list_subrel_metaterm(mt) matches just(subrel) -> nothing()
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

  return
     case errorMsg of
     | just(str) -> left(str)
     | nothing() -> right(proof)
     end;
}


--Try to find the subrelation term for is_list in a given metaterm
function get_is_list_subrel_metaterm
Maybe<Term> ::= tm::Metaterm
{
  return
     case tm of
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
function theorem__symmetry
Either<String [ProofCommand]> ::=
   h::HHint depth::Maybe<Integer> args::[ApplyArg] withs::[(String, Term)]
   --The hypotheses in the current context
   hyps::[(String, Metaterm)]
   --Types of known productions
   knownProds::[(String, Type)]
{
  --Theorem symmetry[A] : forall (A B : A), A = B -> B = A

  local num::String = toString(genInt());
  local name_Assert::String = "$Assert_" ++ num;
  local hyp1::String = "$Hyp_" ++ num;

  local trms::(Term, Term) =
        case get_arg_hyp_metaterm(head(args), hyps),
             findAssociated("A", withs),
             findAssociated("B", withs) of
          | _, just(atrm), just(btrm) -> (atrm, btrm)
          | just(eqMetaterm(atrm, btrm)), _, _ ->(new(atrm), new(btrm))
          | just(termMetaterm(applicationTerm(_,
                    consTermList(atrm, singleTermList(btrm))), _)), _, _ ->
            (new(atrm), new(btrm))
          | _, _, _ -> error("Should not access trms in presence of errors")
          end;
  local isNt::Boolean =
        case get_arg_hyp_metaterm(head(args), hyps) of
        | just(eqMetaterm(_, _)) -> false
        | just(termMetaterm(applicationTerm(_,
                  consTermList(atrm, singleTermList(btrm))), _)) ->
          true
        | nothing() ->
          case trms of
          | (nameTerm(str, _), _)
            when isProd(str) -> true
          | (_, nameTerm(str, _))
            when isProd(str) -> true
          | (applicationTerm(nameTerm(str, _), _), _)
            when isProd(str) -> true
          | (_, applicationTerm(nameTerm(str, _), _))
            when isProd(str) -> true
          | _ -> false
          end
        | _ -> false
        end;
  local tyNT::Maybe<Type> =
      case get_arg_hyp_metaterm(head(args), hyps) of
      | just(termMetaterm(applicationTerm(nameTerm(str, _), _), _)) ->
        just(structureEqToType(str))
      | nothing() -> --check trms for productions
        case trms of
        | (nameTerm(str, _), _) when isProd(str) ->
          case findAssociated(str, knownProds) of
          | nothing() -> nothing()
          | just(ty) -> just(ty.resultType)
          end
        | (_, nameTerm(str, _)) when isProd(str) ->
          case findAssociated(str, knownProds) of
          | nothing() -> nothing()
          | just(ty) -> just(ty.resultType)
          end
        | (applicationTerm(nameTerm(str, _), _), _) when isProd(str) ->
          case findAssociated(str, knownProds) of
          | nothing() -> nothing()
          | just(ty) -> just(ty.resultType)
          end
        | (_, applicationTerm(nameTerm(str, _), _)) when isProd(str) ->
          case findAssociated(str, knownProds) of
          | nothing() -> nothing()
          | just(ty) -> just(ty.resultType)
          end
        | (nameTerm(tr1, _), nameTerm(tr2, _)) -> --go search for WPD assumptions
          case find_WPD_nt_hyp(tr1, hyps) of
          | just((_, termMetaterm(applicationTerm(nameTerm(str, _), _), _))) -> 
            just(wpdNt_type(str))
          | _ -> 
            case find_WPD_nt_hyp(tr1, hyps) of
            | just((_, termMetaterm(applicationTerm(nameTerm(str, _), _), _))) -> 
              just(wpdNt_type(str))
            | _ -> nothing()
            end
          end
        | _ -> nothing()
        end
      | _ -> nothing()
      end;
  local proof::[ProofCommand] =
        if isNt
        then [
              applyTactic(h, depth,
                 clearable(false, typeToStructureEq_Symm(tyNT.fromJust), []),
                 args, [("T1", trms.1), ("T2", trms.2)])
             ]
        else [
              assertTactic(
                 nameHint(name_Assert), nothing(),
                 bindingMetaterm(
                    forallBinder(),
                    [("$A" ++ num, nothing()), ("$B" ++ num, nothing())],
                    eqMetaterm(
                       nameTerm("$A" ++ num, nothing()),
                       nameTerm("$B" ++ num, nothing())))),
              --prove assertion
              introsTactic([hyp1]),
              caseTactic(noHint(), hyp1, false),
              searchTactic(),
              --use assertion
              applyTactic(h, depth,
                 clearable(false, name_Assert, []), args,
                 [("$A" ++ num, trms.1), ("$B" ++ num, trms.2)])
             ];

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
          | just(eqMetaterm(atrm1, btrm1)), just(atrm2), just(btrm2) ->
            if termsEqual(atrm1, atrm2)
            then if termsEqual(btrm1, btrm2)
                 then nothing()
                 else just("While matching argument #1:\nUnification failure for argument B")
            else just("While matching argument #1:\nUnification failure for argument A")
          | just(eqMetaterm(atrm1, btrm1)), just(atrm2), nothing() ->
            if termsEqual(atrm1, atrm2)
            then nothing()
            else just("While matching argument #1:\nUnification failure for argument A")
          | just(eqMetaterm(atrm1, btrm1)), nothing(), just(btrm2) ->
            if termsEqual(btrm1, btrm2)
            then nothing()
            else just("While matching argument #1:\nUnification failure for argument B")
          | just(eqMetaterm(atrm1, btrm1)), nothing(), nothing() ->
            nothing()
          | just(termMetaterm(applicationTerm(nameTerm(structEq, _),
                    consTermList(atrm1, singleTermList(btrm1))), _)),
            just(atrm2), just(btrm2) when isStructureEqName(structEq) ->
            if termsEqual(atrm1, atrm2)
            then if termsEqual(btrm1, btrm2)
                 then nothing()
                 else just("While matching argument #1:\nUnification failure for argument B")
            else just("While matching argument #1:\nUnification failure for argument A")
          | just(termMetaterm(applicationTerm(nameTerm(structEq, _),
                    consTermList(atrm1, singleTermList(btrm1))), _)),
            just(atrm2), nothing() when isStructureEqName(structEq) ->
            if termsEqual(atrm1, atrm2)
            then nothing()
            else just("While matching argument #1:\nUnification failure for argument A")
          | just(termMetaterm(applicationTerm(nameTerm(structEq, _),
                    consTermList(atrm1, singleTermList(btrm1))), _)),
            nothing(), just(btrm2) when isStructureEqName(structEq) ->
            if termsEqual(btrm1, btrm2)
            then nothing()
            else just("While matching argument #1:\nUnification failure for argument B")
          | just(termMetaterm(applicationTerm(nameTerm(structEq, _),
                    consTermList(atrm1, singleTermList(btrm1))), _)),
            nothing(), nothing() when isStructureEqName(structEq) ->
            nothing()
          | just(_), _, _ -> just("While matching argument #1:\nUnification failure")
          | nothing(), just(atrm), just(btrm) -> nothing()
          end
        | _ -> just("symmetry expects 1 argument but was given " ++
                    toString(length(args)))
        end;

  return
     case errorMsg of
     | just(str) -> left(str)
     | nothing() ->
       if (isNt && tyNT.isJust) || !isNt
       then right(proof)
       else left("Could not determine tree type for symmetry")
     end;
}

