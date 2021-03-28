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
        | _ -> just("is_list_append expects 2 arguments but has " ++
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





--Find the metaterm which is the body of a hypothesis
function get_arg_hyp_metaterm
Maybe<Metaterm> ::= arg::ApplyArg hyps::[(String, Metaterm)]
{
  return
     case arg of
     | hypApplyArg(hyp_name, instantiation) ->
       findAssociated(hyp_name, hyps)
     | starApplyArg(hyp_name, instantiation) ->
       findAssociated(hyp_name, hyps)
     end;
}

